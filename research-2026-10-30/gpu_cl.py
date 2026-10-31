"""gpu_cl: a minimal OpenCL binding (ctypes + numpy) for GPU kernels on this machine, with nothing to install.

The NVIDIA driver ships OpenCL.dll and compiles OpenCL C at run time, so kernels are plain source strings.

    from gpu_cl import GPU
    g = GPU()                                   # first GPU whose platform name contains "NVIDIA" (else any GPU)
    prog = g.build(src)                         # raises with the build log on errors
    k = prog.kernel("name")
    buf = g.buffer(numpy_array)                 # device copy of the array
    k(global_size, buf, np.int32(5), ...)       # buffers and numpy scalars; blocks until done
    g.read(buf, numpy_array)                    # copy back

Keep single launches well under 2 s: Windows resets the driver (TDR) when a kernel runs longer.
"""
import ctypes as C

import numpy as np

cl = C.WinDLL("OpenCL")
P, I, U, Z, UL = C.c_void_p, C.c_int32, C.c_uint32, C.c_size_t, C.c_uint64
PI = C.POINTER(I)

for name, res, args in [
    ("clGetPlatformIDs", I, [U, C.POINTER(P), C.POINTER(U)]),
    ("clGetPlatformInfo", I, [P, U, Z, P, C.POINTER(Z)]),
    ("clGetDeviceIDs", I, [P, UL, U, C.POINTER(P), C.POINTER(U)]),
    ("clGetDeviceInfo", I, [P, U, Z, P, C.POINTER(Z)]),
    ("clCreateContext", P, [P, U, C.POINTER(P), P, P, PI]),
    ("clCreateCommandQueue", P, [P, P, UL, PI]),
    ("clCreateProgramWithSource", P, [P, U, C.POINTER(C.c_char_p), C.POINTER(Z), PI]),
    ("clBuildProgram", I, [P, U, C.POINTER(P), C.c_char_p, P, P]),
    ("clGetProgramBuildInfo", I, [P, P, U, Z, P, C.POINTER(Z)]),
    ("clCreateKernel", P, [P, C.c_char_p, PI]),
    ("clCreateBuffer", P, [P, UL, Z, P, PI]),
    ("clSetKernelArg", I, [P, U, Z, P]),
    ("clEnqueueNDRangeKernel", I, [P, P, U, C.POINTER(Z), C.POINTER(Z), C.POINTER(Z), U, P, P]),
    ("clEnqueueReadBuffer", I, [P, P, U, Z, Z, P, U, P, P]),
    ("clEnqueueWriteBuffer", I, [P, P, U, Z, Z, P, U, P, P]),
    ("clFinish", I, [P]),
    ("clReleaseMemObject", I, [P]),
    ("clReleaseKernel", I, [P]),
    ("clReleaseProgram", I, [P]),
]:
    f = getattr(cl, name)
    f.restype, f.argtypes = res, args

GPU_TYPE, MEM_RW, MEM_COPY = 4, 1, 0x20
PLATFORM_NAME, DEVICE_NAME, BUILD_LOG = 0x0902, 0x102B, 0x1183


class CLError(RuntimeError):
    pass


def check(err, what):
    e = err.value if isinstance(err, I) else err
    if e != 0:
        raise CLError(f"{what} failed with OpenCL error {e}")


def _info(fn, obj, key):
    buf = C.create_string_buffer(1024)
    check(fn(obj, key, 1024, buf, None), fn.__name__)
    return buf.value.decode(errors="replace")


class Buffer:
    def __init__(self, gpu, array):
        self.gpu, self.nbytes, self.dtype = gpu, array.nbytes, array.dtype
        err = I()
        a = np.ascontiguousarray(array)
        self.mem = cl.clCreateBuffer(gpu.ctx, MEM_RW | MEM_COPY, a.nbytes, a.ctypes.data, C.byref(err))
        check(err, "clCreateBuffer")

    def __del__(self):
        if getattr(self, "mem", None):
            cl.clReleaseMemObject(self.mem)


class Kernel:
    def __init__(self, gpu, prog, name):
        self.gpu, self.name = gpu, name
        err = I()
        self.k = cl.clCreateKernel(prog, name.encode(), C.byref(err))
        check(err, f"clCreateKernel({name})")

    def __call__(self, global_size, *args, local_size=None):
        keep = []
        for i, a in enumerate(args):
            if isinstance(a, Buffer):
                h = P(a.mem)
                keep.append(h)
                check(cl.clSetKernelArg(self.k, i, C.sizeof(P), C.byref(h)), f"{self.name} arg {i}")
            else:
                v = np.asarray(a)
                if v.ndim or v.dtype == object:
                    raise TypeError(f"{self.name} arg {i}: pass a Buffer or a numpy scalar")
                keep.append(v)
                check(cl.clSetKernelArg(self.k, i, v.nbytes, v.ctypes.data), f"{self.name} arg {i}")
        gs = (Z * 1)(global_size)
        ls = (Z * 1)(local_size) if local_size else None
        check(cl.clEnqueueNDRangeKernel(self.gpu.queue, self.k, 1, None, gs, ls, 0, None, None), self.name)
        check(cl.clFinish(self.gpu.queue), f"{self.name} (run)")

    def __del__(self):
        if getattr(self, "k", None):
            cl.clReleaseKernel(self.k)


class Program:
    def __init__(self, gpu, handle):
        self.gpu, self.p = gpu, handle

    def kernel(self, name):
        return Kernel(self.gpu, self.p, name)


class GPU:
    def __init__(self, prefer="NVIDIA"):
        n = U()
        check(cl.clGetPlatformIDs(0, None, C.byref(n)), "clGetPlatformIDs")
        plats = (P * n.value)()
        check(cl.clGetPlatformIDs(n, plats, None), "clGetPlatformIDs")
        found = []
        for p in plats:
            nd = U()
            if cl.clGetDeviceIDs(p, GPU_TYPE, 0, None, C.byref(nd)) != 0 or not nd.value:
                continue
            devs = (P * nd.value)()
            check(cl.clGetDeviceIDs(p, GPU_TYPE, nd, devs, None), "clGetDeviceIDs")
            found += [(prefer.lower() not in _info(cl.clGetPlatformInfo, p, PLATFORM_NAME).lower(), d) for d in devs]
        if not found:
            raise CLError("no OpenCL GPU found")
        self.dev = P(min(found, key=lambda x: x[0])[1])
        self.name = _info(cl.clGetDeviceInfo, self.dev, DEVICE_NAME)
        err = I()
        self.ctx = cl.clCreateContext(None, 1, C.byref(self.dev), None, None, C.byref(err))
        check(err, "clCreateContext")
        self.queue = cl.clCreateCommandQueue(self.ctx, self.dev, 0, C.byref(err))
        check(err, "clCreateCommandQueue")

    def build(self, src, options=""):
        err = I()
        s = C.c_char_p(src.encode())
        prog = cl.clCreateProgramWithSource(self.ctx, 1, C.byref(s), None, C.byref(err))
        check(err, "clCreateProgramWithSource")
        if cl.clBuildProgram(prog, 1, C.byref(self.dev), options.encode(), None, None) != 0:
            size = Z()
            cl.clGetProgramBuildInfo(prog, self.dev, BUILD_LOG, 0, None, C.byref(size))
            log = C.create_string_buffer(size.value + 1)
            cl.clGetProgramBuildInfo(prog, self.dev, BUILD_LOG, size.value, log, None)
            raise CLError("build failed:\n" + log.value.decode(errors="replace"))
        return Program(self, prog)

    def buffer(self, array):
        return Buffer(self, array)

    def read(self, buf, array):
        assert array.flags.c_contiguous and array.nbytes == buf.nbytes
        check(cl.clEnqueueReadBuffer(self.queue, buf.mem, 1, 0, buf.nbytes, array.ctypes.data, 0, None, None),
              "read")
        return array

    def write(self, buf, array):
        a = np.ascontiguousarray(array)
        assert a.nbytes == buf.nbytes
        check(cl.clEnqueueWriteBuffer(self.queue, buf.mem, 1, 0, buf.nbytes, a.ctypes.data, 0, None, None),
              "write")


if __name__ == "__main__":
    g = GPU()
    print("device:", g.name)
    prog = g.build("__kernel void axpy(__global float *y, __global const float *x, float a, int n) {"
                   "  int i = get_global_id(0); if (i < n) y[i] += a * x[i]; }")
    n = 1 << 20
    x = np.arange(n, dtype=np.float32)
    y = np.ones(n, dtype=np.float32)
    bx, by = g.buffer(x), g.buffer(y)
    prog.kernel("axpy")(n, by, bx, np.float32(2.0), np.int32(n))
    g.read(by, y)
    print("axpy ok:", bool(np.allclose(y, 1 + 2 * x)))
