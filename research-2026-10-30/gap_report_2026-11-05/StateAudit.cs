using System;
using System.IO;
using System.IO.Compression;
using System.Linq;
using System.Collections.Generic;

public static class StateAudit {
    static List<int>[] adj;
    static int n, k;
    static bool kempe;
    static HashSet<long> remaining;
    static long Encode(int[] c) {
        int[] rename = new int[k+1]; int next = 0; long code=0, place=1;
        foreach (int a in c) {
            int b=0;
            if(a>0) { if(rename[a]==0) rename[a]=++next; b=rename[a]; }
            code+=place*b; place*=k+1;
        }
        return code;
    }
    static int[] Decode(long code) {
        int[] c = new int[n];
        for(int i=0;i<n;i++) {c[i]=(int)(code%(k+1)); code/=k+1;}
        return c;
    }
    static int[] Count(int[] c, int x) {
        int[] count = new int[k+1];
        foreach(int y in adj[x]) if(c[y]>0) count[c[y]]++;
        return count;
    }
    static void Enumerate(int[] c, int h, int pos, int maxc) {
        if(pos==n) {remaining.Add(Encode(c)); return;}
        if(pos==h) {c[pos]=0; Enumerate(c,h,pos+1,maxc); return;}
        for(int a=1; a<=Math.Min(k,maxc+1); a++) {
            if(adj[pos].Any(y=>y<pos && c[y]==a)) continue;
            c[pos]=a; Enumerate(c,h,pos+1,Math.Max(a,maxc));
        }
    }
    static IEnumerable<long> Moves(int[] c) {
        int h=Array.IndexOf(c,0); int[] count=Count(c,h);
        foreach(int y in adj[h]) if(count[c[y]]==1) {
            int a=c[y]; c[h]=a; c[y]=0;
            yield return Encode(c);
            c[y]=a; c[h]=0;
        }
        if(!kempe) yield break;
        for(int a=1;a<=k;a++) for(int b=a+1;b<=k;b++) {
            bool[] seen=new bool[n];
            for(int x=0;x<n;x++) if(!seen[x] && (c[x]==a || c[x]==b)) {
                List<int> component=new List<int>() {x}; seen[x]=true;
                for(int i=0;i<component.Count;i++) foreach(int y in adj[component[i]])
                    if(!seen[y] && (c[y]==a || c[y]==b)) {seen[y]=true;component.Add(y);}
                foreach(int y in component) c[y]=a+b-c[y];
                yield return Encode(c);
                foreach(int y in component) c[y]=a+b-c[y];
            }
        }
    }
    static string Defect(int[] c) {
        int h=Array.IndexOf(c,0);
        int[][] counts=Enumerable.Range(0,n).Select(x=>Count(c,x)).ToArray();
        List<int>[] arcs=Enumerable.Range(0,n).Select(x=>adj[x].Where(y=>c[y]>0 && counts[x][c[y]]==1).ToList()).ToArray();
        List<int> reach=new List<int>() {h}; bool[] seen=new bool[n]; seen[h]=true;
        for(int i=0;i<reach.Count;i++) foreach(int y in arcs[reach[i]]) if(!seen[y]) {seen[y]=true;reach.Add(y);}
        foreach(int x in reach) if(counts[x].Count(v=>v>0)<k-(x==h?0:1)) return "unsaturated " + x;
        foreach(int g in reach) foreach(int f in arcs[g]) foreach(int w in arcs[f])
            if(g!=w && !adj[g].Contains(w) && arcs[w].Contains(f)) return "double " + g + " " + f + " " + w;
        return null;
    }
    public static void Atlas(string atlasPath, int colours, bool useKempe, int maxN, string outputPath, bool doubleOnly) {
        k=colours; kempe=useKempe;
        int graphCount=0, totalStates=0, closed=0;
        DateTime started=DateTime.UtcNow;
        using(FileStream fs=File.OpenRead(atlasPath)) using(GZipStream gz=new GZipStream(fs,CompressionMode.Decompress)) using(StreamReader rd=new StreamReader(gz)) {
            string line=rd.ReadLine();
            while(line!=null) {
                if(!line.StartsWith("GRAPH ")) throw new Exception(line);
                int id=int.Parse(line.Split(' ')[1]);
                n=int.Parse(rd.ReadLine().Split(' ')[1]);
                adj=Enumerable.Range(0,n).Select(_=>new List<int>()).ToArray();
                List<string> edges=new List<string>();
                while((line=rd.ReadLine())!=null && !line.StartsWith("GRAPH ")) {
                    string[] pair=line.Split(new char[]{' '},StringSplitOptions.RemoveEmptyEntries);
                    int a=int.Parse(pair[0]), b=int.Parse(pair[1]); adj[a].Add(b);adj[b].Add(a);edges.Add("["+a+","+b+"]");
                }
                if(n<2 || n>maxN) continue;
                HashSet<int> connected=new HashSet<int>() {0}; List<int> cq=new List<int>() {0};
                for(int i=0;i<cq.Count;i++) foreach(int y in adj[cq[i]]) if(connected.Add(y)) cq.Add(y);
                if(cq.Count<n) continue;
                graphCount++;
                remaining=new HashSet<long>();
                for(int h=0;h<n;h++) Enumerate(new int[n],h,0,0);
                totalStates+=remaining.Count;
                while(remaining.Count>0) {
                    long root=remaining.Min(); remaining.Remove(root);
                    List<long> q=new List<long>() {root}; HashSet<long> comp=new HashSet<long>() {root};
                    bool free=false; string defect=null; int[] defectCol=null;
                    for(int i=0;i<q.Count;i++) {
                        int[] c=Decode(q[i]); int h=Array.IndexOf(c,0);
                        if(Count(c,h).Count(v=>v>0)<k) free=true;
                        if(defect==null) {defect=Defect(c);if(doubleOnly && defect!=null && !defect.StartsWith("double")) defect=null;if(defect!=null) defectCol=(int[])c.Clone();}
                        foreach(long next in Moves(c)) if(comp.Add(next)) {
                            if(!remaining.Remove(next)) throw new Exception("Missing state");
                            q.Add(next);
                        }
                    }
                    if(!free) {
                        closed++;
                        if(defect!=null) {
                            string json="{\n\"atlas_id\":"+id+",\n\"n\":"+n+",\n\"k\":"+k+",\n\"kempe\":"+kempe.ToString().ToLower()+",\n\"edges\":["+string.Join(",",edges)+"],\n\"colouring_zero_is_hole\":["+string.Join(",",defectCol)+"],\n\"defect\":\""+defect+"\",\n\"component_size_mod_colour_permutations\":"+comp.Count+",\n\"states\":["+string.Join(",",comp.OrderBy(x=>x).Select(x=>"["+string.Join(",",Decode(x))+"]"))+" ]\n}";
                            File.WriteAllText(outputPath,json);
                            Console.WriteLine("COUNTEREXAMPLE graph="+id+" k="+k+" kempe="+kempe+" defect="+defect+" states="+comp.Count+" output="+outputPath);
                            return;
                        }
                    }
                }
                if(graphCount%100==0) Console.WriteLine("progress graphs="+graphCount+" states="+totalStates+" closed="+closed+" seconds="+(DateTime.UtcNow-started).TotalSeconds);
            }
        }
        Console.WriteLine("FINISHED graphs="+graphCount+" states="+totalStates+" closed="+closed+" seconds="+(DateTime.UtcNow-started).TotalSeconds);
    }
}
