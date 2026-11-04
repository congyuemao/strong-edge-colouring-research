using System;
using System.IO;
using System.Linq;
using System.Collections.Generic;

public static class Experiments {
    static int K=20;
    public static List<int[]> GQEdges() {
        List<int[]> points=new List<int[]>();
        for(int i=1;i<81;i++) {
            int t=i; int[] p=new int[4];
            for(int j=0;j<4;j++) {p[j]=t%3;t/=3;}
            if(p.First(x=>x!=0)==1) points.Add(p);
        }
        Dictionary<string,int> index=new Dictionary<string,int>();
        for(int i=0;i<points.Count;i++) index[string.Join(",",points[i])]=i;
        HashSet<string> lines=new HashSet<string>();
        for(int i=0;i<points.Count;i++) for(int j=i+1;j<points.Count;j++) {
            int[] a=points[i],b=points[j];
            if((a[0]*b[1]-a[1]*b[0]+a[2]*b[3]-a[3]*b[2])%3!=0) continue;
            HashSet<int> span=new HashSet<int>();
            for(int s=0;s<3;s++) for(int t=0;t<3;t++) if(s+t>0) {
                int[] v=Enumerable.Range(0,4).Select(z=>(s*a[z]+t*b[z])%3).ToArray();
                int inv=v.First(x=>x!=0); // inverses of 1,2 in F_3 are themselves.
                v=v.Select(x=>x*inv%3).ToArray();
                span.Add(index[string.Join(",",v)]);
            }
            if(span.Count!=4) throw new Exception("line size");
            lines.Add(string.Join(",",span.OrderBy(x=>x)));
        }
        List<int[]> edges=new List<int[]>(); int lineNo=points.Count;
        foreach(string line in lines.OrderBy(x=>x)) {
            foreach(string point in line.Split(',')) edges.Add(new int[]{int.Parse(point),lineNo});
            lineNo++;
        }
        if(points.Count!=40 || lines.Count!=40 || edges.Count!=160) throw new Exception("GQ size");
        return edges;
    }
    public static List<int>[] Conflict(List<int[]> edges) {
        int n=edges.Max(e=>e.Max())+1;
        bool[,] baseAdj=new bool[n,n];
        foreach(int[] e in edges) baseAdj[e[0],e[1]]=baseAdj[e[1],e[0]]=true;
        List<int>[] adj=edges.Select(e=>new List<int>()).ToArray();
        for(int i=0;i<edges.Count;i++) for(int j=0;j<i;j++) {
            int[] e=edges[i],f=edges[j];
            if(e.Intersect(f).Any() || e.Any(x=>f.Any(y=>baseAdj[x,y]))) {adj[i].Add(j);adj[j].Add(i);}
        }
        return adj;
    }
    static int Girth(List<int[]> edges) {
        int n=edges.Max(e=>e.Max())+1, ans=int.MaxValue;
        List<int>[] adj=Enumerable.Range(0,n).Select(x=>new List<int>()).ToArray();
        foreach(int[] e in edges) {adj[e[0]].Add(e[1]);adj[e[1]].Add(e[0]);}
        for(int root=0;root<n;root++) {
            int[] dist=Enumerable.Repeat(-1,n).ToArray(),par=Enumerable.Repeat(-1,n).ToArray();
            List<int> q=new List<int>(){root};dist[root]=0;
            for(int i=0;i<q.Count;i++) foreach(int y in adj[q[i]]) {
                int x=q[i];
                if(dist[y]<0) {dist[y]=dist[x]+1;par[y]=x;q.Add(y);}
                else if(par[x]!=y) ans=Math.Min(ans,dist[x]+dist[y]+1);
            }
        }
        return ans;
    }
    public static void Geometry() {
        List<int[]> edges=GQEdges();List<int>[] adj=Conflict(edges);
        int near=0,far=0,opposite=0;
        for(int f=0;f<edges.Count;f++) {
            if(adj[f].Count!=24) throw new Exception("degree");
            Dictionary<int,HashSet<int>> intersections=new Dictionary<int,HashSet<int>>();
            foreach(int w in adj[f]) {
                HashSet<int> common=new HashSet<int>(adj[f].Where(x=>x==w || adj[w].Contains(x)));
                bool shared=edges[f].Intersect(edges[w]).Any();
                if(common.Count!=(shared?15:6)) throw new Exception("overlap");
                intersections[w]=common;
                if(shared) near++; else far++;
            }
            foreach(int a in adj[f].Where(x=>edges[x].Contains(edges[f][0])))
                foreach(int b in adj[f].Where(x=>edges[x].Contains(edges[f][1]))) {
                    if(intersections[a].Intersect(intersections[b]).Count()!=6) throw new Exception("opposite");
                    opposite++;
                }
        }
        Console.WriteLine("Geometry: vertices=80 edges="+edges.Count+" girth="+Girth(edges)+" conflict_degree=24 near_ordered="+near+" far_ordered="+far+" opposite_end_tests="+opposite+" failures=0");
    }
    static int[][] Multiplicities(List<int>[] adj,int[] col,bool closed) {
        int[][] mult=adj.Select(x=>new int[K]).ToArray();
        for(int x=0;x<adj.Length;x++) {
            foreach(int y in adj[x]) if(col[y]>=0) mult[x][col[y]]++;
            if(closed && col[x]>=0) mult[x][col[x]]++;
        }
        return mult;
    }
    static bool Valid(List<int>[] adj,int[] col) {
        return Enumerable.Range(0,col.Length).All(x=>col[x]<0 || adj[x].All(y=>col[y]!=col[x]));
    }
    public static int HoleDepth(List<int>[] adj,int[] start,int limit) {
        List<int[]> q=new List<int[]>(){(int[])start.Clone()};
        List<int> depths=new List<int>(){0}; HashSet<string> seen=new HashSet<string>(){string.Join(",",start)};
        for(int i=0;i<q.Count;i++) {
            int[] col=q[i];int h=Array.IndexOf(col,-1),d=depths[i];
            int[] mult=new int[K]; foreach(int y in adj[h]) mult[col[y]]++;
            if(mult.Any(x=>x==0)) return d;
            if(d>=limit) continue;
            foreach(int y in adj[h]) if(mult[col[y]]==1) {
                int[] next=(int[])col.Clone();next[h]=col[y];next[y]=-1;
                if(!Valid(adj,next)) throw new Exception("illegal hole move");
                if(seen.Add(string.Join(",",next))) {q.Add(next);depths.Add(d+1);}
            }
        }
        return -1;
    }
    static string JsonState(List<int[]> edges,int[] col,string extra) {
        return "{\n\"edges\":["+string.Join(",",edges.Select(e=>"["+string.Join(",",e)+"]"))+"],\n\"e\":"+Array.IndexOf(col,-1)+",\n\"colouring\":["+string.Join(",",col)+"],\n"+extra+"\n}";
    }
    static int[] Greedy(List<int>[] adj,int h,Random rng) {
        for(int attempt=0;attempt<1000;attempt++) {
            int[] col=Enumerable.Repeat(-2,adj.Length).ToArray();col[h]=-1;
            List<int> nb=adj[h].OrderBy(x=>rng.Next()).ToList();
            bool failed=false;
            for(int i=0;i<nb.Count;i++) {
                int x=nb[i];
                List<int> available=Enumerable.Range(0,K).Where(a=>adj[x].All(y=>col[y]!=a)).ToList();
                if(i<K) col[x]=i;
                else if(available.Count>0) col[x]=available[rng.Next(available.Count)];
                else {failed=true;break;}
            }
            if(failed) continue;
            while(col.Any(x=>x==-2)) {
                int x=Enumerable.Range(0,col.Length).Where(y=>col[y]==-2).OrderByDescending(y=>adj[y].Where(z=>col[z]>=0).Select(z=>col[z]).Distinct().Count()).ThenBy(y=>rng.Next()).First();
                List<int> available=Enumerable.Range(0,K).Where(a=>adj[x].All(y=>col[y]!=a)).ToList();
                if(available.Count==0) {failed=true;break;}
                col[x]=available[rng.Next(available.Count)];
            }
            if(!failed && Valid(adj,col)) return col;
        }
        throw new Exception("greedy failed");
    }
    public static void Hunt(int seconds,int seed,string outputPath,bool allVertices) {
        List<int[]> edges=GQEdges();List<int>[] adj=Conflict(edges);int m=adj.Length,h=0;
        Random rng=new Random(seed);int[] col=Greedy(adj,h,rng);
        bool[] active=Enumerable.Range(0,m).Select(x=>allVertices || x==h || adj[h].Contains(x)).ToArray();
        int[][] closed=Enumerable.Range(0,m).Select(x=>adj[x].Concat(new int[]{x}).ToArray()).ToArray();
        int[][] mult=Multiplicities(adj,col,true);int[,] tabu=new int[m,K];
        int missing=Enumerable.Range(0,m).Where(x=>active[x]).Sum(x=>mult[x].Count(t=>t==0));
        int conflicts=0,best=1000000;const int W=3;
        long iteration=0;DateTime started=DateTime.UtcNow,lastLog=started;
        while((DateTime.UtcNow-started).TotalSeconds<seconds) {
            int energy=W*conflicts+missing;
            if(energy<best) {best=energy;if(best<20) Console.WriteLine("best="+best+" conflicts="+conflicts+" missing="+missing+" iter="+iteration);}
            if(energy==0) {
                if(!Valid(adj,col)) throw new Exception("invalid witness");
                int depth=HoleDepth(adj,col,3);
                File.WriteAllText(outputPath,JsonState(edges,col,"\"seed\":"+seed+",\n\"active_all_vertices\":"+allVertices.ToString().ToLower()+",\n\"shortest_hole_depth_up_to_3\":"+depth));
                Console.WriteLine("FOUND depth="+depth+" seconds="+(DateTime.UtcNow-started).TotalSeconds+" output="+outputPath);
                PairCore(adj,col,true);return;
            }
            List<int[]> proposals=new List<int[]>();
            if(conflicts>0 && (missing==0 || rng.NextDouble()<0.45)) {
                List<int> bad=Enumerable.Range(0,m).Where(x=>x!=h && adj[x].Any(y=>col[y]==col[x])).ToList();
                int chosen=bad[rng.Next(bad.Count)];
                for(int a=0;a<K;a++) if(a!=col[chosen]) proposals.Add(new int[]{chosen,a});
            } else {
                List<int> bad=Enumerable.Range(0,m).Where(x=>active[x] && mult[x].Any(t=>t==0)).ToList();
                int center=bad[rng.Next(bad.Count)];
                List<int> absent=Enumerable.Range(0,K).Where(z=>mult[center][z]==0).ToList();
                int a=absent[rng.Next(absent.Count)];
                foreach(int candidate in closed[center]) if(candidate!=h) proposals.Add(new int[]{candidate,a});
            }
            int bx=-1,bc=-1,bDelta=int.MaxValue,ties=0;
            bool noise=rng.NextDouble()<0.025;
            foreach(int[] proposal in proposals.OrderBy(x=>rng.Next())) {
                int x=proposal[0],a=proposal[1],old=col[x];
                if(tabu[x,a]>iteration && proposals.Count>1) continue;
                int delta=W*(adj[x].Count(y=>col[y]==a)-adj[x].Count(y=>col[y]==old));
                foreach(int y in closed[x]) if(active[y]) {if(mult[y][old]==1) delta++;if(mult[y][a]==0) delta--;}
                if(noise) {bx=x;bc=a;break;}
                if(delta<bDelta || (delta==bDelta && rng.Next(++ties)==0)) {if(delta<bDelta) ties=1;bx=x;bc=a;bDelta=delta;}
            }
            if(bx<0) {int[] p=proposals[rng.Next(proposals.Count)];bx=p[0];bc=p[1];}
            int before=col[bx];
            conflicts+=adj[bx].Count(y=>col[y]==bc)-adj[bx].Count(y=>col[y]==before);
            foreach(int y in closed[bx]) {
                if(active[y]) {if(mult[y][before]==1) missing++;if(mult[y][bc]==0) missing--;}
                mult[y][before]--;mult[y][bc]++;
            }
            tabu[bx,before]=(int)iteration+3+rng.Next(8);col[bx]=bc;iteration++;
            if((DateTime.UtcNow-lastLog).TotalSeconds>=15) {Console.WriteLine("progress seconds="+(DateTime.UtcNow-started).TotalSeconds+" best="+best+" current="+(W*conflicts+missing)+" iterations="+iteration);lastLog=DateTime.UtcNow;}
        }
        Console.WriteLine("NOT FOUND seconds="+seconds+" best="+best+" iterations="+iteration);
    }
    public static int PairCore(List<int>[] adj,int[] col,bool verbose) {
        int m=col.Length,h=Array.IndexOf(col,-1),success=0,initialSeparable=0,minCore=m,maxCore=0;
        for(int a=0;a<K;a++) for(int b=a+1;b<K;b++) {
            int[] component=Enumerable.Repeat(-1,m).ToArray();int nextId=0;
            for(int x=0;x<m;x++) if(component[x]<0 && (col[x]==a || col[x]==b)) {
                List<int> q=new List<int>(){x};component[x]=nextId;
                for(int i=0;i<q.Count;i++) foreach(int y in adj[q[i]]) if(component[y]<0 && (col[y]==a || col[y]==b)) {component[y]=nextId;q.Add(y);}
                nextId++;
            }
            bool[] keep=new bool[m];int[] threshold=new int[m];
            for(int x=0;x<m;x++) if(col[x]!=a && col[x]!=b) {
                HashSet<int> ca=new HashSet<int>(adj[x].Where(y=>col[y]==a).Select(y=>component[y]));
                keep[x]=adj[x].Any(y=>col[y]==b && ca.Contains(component[y]));
                int fixedDegree=adj[x].Count(y=>col[y]==a || col[y]==b);
                threshold[x]=2*(K-2)-adj[x].Count+fixedDegree;
            }
            if(!keep[h]) initialSeparable++;
            bool changed=true;
            while(changed) {changed=false;for(int x=0;x<m;x++) if(keep[x] && adj[x].Count(y=>keep[y])<threshold[x]) {keep[x]=false;changed=true;}}
            int size=keep.Count(x=>x);minCore=Math.Min(minCore,size);maxCore=Math.Max(maxCore,size);
            if(!keep[h]) success++;
        }
        if(verbose) Console.WriteLine("pair_core repair_pairs="+success+" initially_separable="+initialSeparable+" min_core="+minCore+" max_core="+maxCore);
        return success;
    }
    public static void RandomChecks(int samples,int seed,string outputPath) {
        List<int[]> edges=GQEdges();List<int>[] adj=Conflict(edges);Random rng=new Random(seed);
        int minPairs=190,maxDepth=0;
        for(int i=0;i<samples;i++) {
            int[] col=Greedy(adj,0,rng);int depth=HoleDepth(adj,col,2);
            int count=PairCore(adj,col,i==0);
            minPairs=Math.Min(minPairs,count);maxDepth=Math.Max(maxDepth,depth);
            if(i==0) File.WriteAllText(outputPath,JsonState(edges,col,"\"sample\":0"));
        }
        Console.WriteLine("random_samples="+samples+" minimum_pair_core_repair_pairs="+minPairs+" maximum_hole_depth="+maxDepth);
    }
    static int Distance(bool[,] adj,int source,int target,int cutoff) {
        int nn=adj.GetLength(0);int[] distance=Enumerable.Repeat(-1,nn).ToArray();
        List<int> queue=new List<int>(){source};distance[source]=0;
        for(int i=0;i<queue.Count;i++) {
            int x=queue[i];if(distance[x]>=cutoff) continue;
            for(int y=0;y<nn;y++) if(adj[x,y] && distance[y]<0) {
                distance[y]=distance[x]+1;if(y==target) return distance[y];queue.Add(y);
            }
        }
        return cutoff+1;
    }
    static List<int[]> PairedGraph(int t,int seed) {
        Random rng=new Random(seed);int nn=5*t;
        bool[,] matrix=new bool[nn,nn];List<int[]> links=new List<int[]>();
        for(int c=0;c<t;c++) for(int j=0;j<2;j++) {
            int l=t+2*c+j,u=3*t+2*c+j;
            matrix[c,l]=matrix[l,c]=true;matrix[c,u]=matrix[u,c]=true;
        }
        for(int round=0;round<3;round++) {
            int[] permutation=null;
            for(int attempt=0;attempt<10000;attempt++) {
                int[] p=Enumerable.Range(0,2*t).OrderBy(x=>rng.Next()).ToArray();
                if(Enumerable.Range(0,2*t).All(i=>!matrix[t+i,3*t+p[i]])) {permutation=p;break;}
            }
            if(permutation==null) throw new Exception("matching generation");
            for(int i=0;i<2*t;i++) {
                int l=t+i,u=3*t+permutation[i];
                matrix[l,u]=matrix[u,l]=true;links.Add(new int[]{l,u});
            }
        }
        int switches=0;
        for(int sweep=0;sweep<100;sweep++) {
            bool clean=true;
            foreach(int idx in Enumerable.Range(0,links.Count).OrderBy(x=>rng.Next())) {
                int a=links[idx][0],b=links[idx][1];matrix[a,b]=matrix[b,a]=false;
                bool bad=Distance(matrix,a,b,5)<=5;
                matrix[a,b]=matrix[b,a]=true;
                if(!bad) continue;clean=false;bool fixedEdge=false;
                foreach(int j in Enumerable.Range(0,links.Count).OrderBy(x=>rng.Next())) {
                    int c=links[j][0],d=links[j][1];
                    if(a==c || b==d || matrix[a,d] || matrix[c,b]) continue;
                    matrix[a,b]=matrix[b,a]=matrix[c,d]=matrix[d,c]=false;
                    bool good=Distance(matrix,a,d,5)>5;
                    if(good) {
                        matrix[a,d]=matrix[d,a]=true;
                        good=Distance(matrix,c,b,5)>5;
                        matrix[a,d]=matrix[d,a]=false;
                    }
                    if(good) {
                        matrix[a,d]=matrix[d,a]=matrix[c,b]=matrix[b,c]=true;
                        links[idx]=new int[]{a,d};links[j]=new int[]{c,b};switches++;fixedEdge=true;break;
                    }
                    matrix[a,b]=matrix[b,a]=matrix[c,d]=matrix[d,c]=true;
                }
                if(!fixedEdge && sweep==99) throw new Exception("girth repair failed");
            }
            if(clean) {
                List<int[]> edges=new List<int[]>();
                for(int i=0;i<nn;i++) for(int j=i+1;j<nn;j++) if(matrix[i,j]) edges.Add(new int[]{i,j});
                Console.WriteLine("paired_graph t="+t+" vertices="+nn+" edges="+edges.Count+" girth="+Girth(edges)+" switches="+switches);
                return edges;
            }
        }
        throw new Exception("girth repair budget");
    }
    static int[] ColourPaired(List<int[]> edges,List<int>[] adj,int t,int seed) {
        Random rng=new Random(seed);int m=edges.Count;
        int[] frozen=Enumerable.Repeat(-2,m).ToArray();
        for(int i=0;i<m;i++) if(edges[i][0]<t && edges[i][1]>=t && edges[i][1]<3*t) frozen[i]=(edges[i][1]-t)%2;
        int h=Enumerable.Range(0,m).First(i=>frozen[i]<0);
        frozen[h]=-1;
        for(int attempt=0;attempt<100;attempt++) {
            int[] col=(int[])frozen.Clone();bool failed=false;
            int[] nb=adj[h].Where(i=>col[i]<0).OrderBy(i=>rng.Next()).ToArray();
            if(nb.Length!=19) throw new Exception("expected 19 remaining neighbours");
            for(int i=0;i<nb.Length;i++) {
                int x=nb[i];List<int> available=Enumerable.Range(2,18).Where(a=>adj[x].All(y=>col[y]!=a)).ToList();
                if(i<18) col[x]=i+2;
                else if(available.Count>0) col[x]=available[rng.Next(available.Count)];
                else {failed=true;break;}
            }
            if(failed) continue;
            while(col.Any(a=>a==-2)) {
                int x=Enumerable.Range(0,m).Where(y=>col[y]==-2).OrderByDescending(y=>adj[y].Where(z=>col[z]>=2).Select(z=>col[z]).Distinct().Count()).ThenBy(y=>rng.Next()).First();
                List<int> available=Enumerable.Range(2,18).Where(a=>adj[x].All(y=>col[y]!=a)).ToList();
                if(available.Count==0) {failed=true;break;}
                col[x]=available[rng.Next(available.Count)];
            }
            if(!failed && Valid(adj,col)) return col;
        }
        throw new Exception("paired colouring failed");
    }
    public static void Paired(int t,int seed,string outputPath) {
        List<int[]> edges=PairedGraph(t,seed);List<int>[] adj=Conflict(edges);int m=edges.Count;
        int[] col=ColourPaired(edges,adj,t,seed);HashSet<int> frozen=new HashSet<int>(Enumerable.Range(0,m).Where(x=>col[x]==0 || col[x]==1));
        foreach(int x in frozen) if(adj[x].Count(y=>frozen.Contains(y))!=1) throw new Exception("pair component");
        foreach(int x in Enumerable.Range(0,m).Where(x=>!frozen.Contains(x))) {
            int expected=edges[x][0]<t?5:6;
            if(adj[x].Count(y=>frozen.Contains(y))!=expected) throw new Exception("fixed degree");
            if(!adj[x].Where(y=>col[y]==0).Any(y=>adj[x].Any(z=>col[z]==1 && adj[y].Contains(z)))) throw new Exception("not inseparable");
        }
        int h=Array.IndexOf(col,-1),depth=HoleDepth(adj,col,2);
        Console.WriteLine("paired_colouring valid=true blocked_hole="+(Multiplicities(adj,col,false)[h].Count(a=>a>0)==20)+" protected_pair=(0,1) protected_core="+(m-frozen.Count)+" internal_degrees=18,19 thresholds=18,17 hole_depth="+depth);
        File.WriteAllText(outputPath,JsonState(edges,col,"\"construction\":\"paired centres\",\n\"t\":"+t+",\n\"seed\":"+seed+",\n\"protected_pair\":[0,1]"));
        PairCore(adj,col,true);
    }
    public static void Audit(List<int[]> edges,int[] col,string tracePath,string transportPath) {
        List<int>[] adj=Conflict(edges);int m=col.Length,h=Array.IndexOf(col,-1);
        if(!Valid(adj,col) || col.Count(a=>a<0)!=1 || adj.Any(row=>row.Count!=24)) throw new Exception("state hypotheses");
        int[][] mult=Multiplicities(adj,col,false);
        if(mult[h].Any(a=>a==0)) throw new Exception("hole not blocked");
        List<int>[] arcs=Enumerable.Range(0,m).Select(x=>adj[x].Where(y=>col[y]>=0 && mult[x][col[y]]==1).ToList()).ToArray();
        HashSet<int> reach=new HashSet<int>(){h};List<int> queue=new List<int>(){h};
        for(int i=0;i<queue.Count;i++) foreach(int y in arcs[queue[i]]) if(reach.Add(y)) queue.Add(y);
        int nn=reach.Count-1,mm=adj[h].Count(y=>reach.Contains(y)),tt=0,yy=0,deficit=0,eta=0,zz=0,bb=0,ll=0;
        foreach(int f in reach.Where(x=>x!=h)) {
            int t=adj[f].Count(v=>!reach.Contains(v)),y=adj[f].Count(g=>g!=h && reach.Contains(g) && mult[g][col[f]]>1),good=0;
            tt+=t;yy+=y;deficit+=19-mult[f].Count(v=>v>0);eta+=mult[f].Where(v=>v>=3).Sum(v=>v-2);
            foreach(int w in adj[f].Where(v=>v!=h && reach.Contains(v))) {
                bool fw=mult[f][col[w]]==1,wf=mult[w][col[f]]==1;
                if(!fw && !wf && f<w) zz++;
                if(fw && wf) {
                    bool bad=adj[f].Any(g=>reach.Contains(g) && g!=w && mult[g][col[f]]==1 && !adj[w].Contains(g));
                    if(bad) bb++;else good++;
                }
            }
            int slack=t+y+(adj[f].Contains(h)?1:0)-3*good;
            if(slack<0) throw new Exception("geometry inequality");ll+=slack;
        }
        int lhs=14*deficit+3*bb,rhs=2*nn+10*mm+3*tt+7*eta+6*zz+ll;
        if(lhs!=rhs) throw new Exception("counting identity");
        Console.WriteLine("quantitative_identity Rprime="+nn+" M="+mm+" T="+tt+" Y="+yy+" deficit="+deficit+" exposed_ordered_pairs="+bb+" eta="+eta+" Z="+zz+" L="+ll+" lhs=rhs="+lhs);
        ProtectedTrace(edges,adj,col,tracePath);
        FindTransport(edges,adj,col,arcs,mult,transportPath);
    }
    static void BuildCore(List<int>[] adj,int[] col,int a,int b,out bool[] initial,out int[] rank,out int[] component) {
        int m=col.Length;component=Enumerable.Repeat(-1,m).ToArray();int nextId=0;
        for(int x=0;x<m;x++) if(component[x]<0 && (col[x]==a || col[x]==b)) {
            List<int> q=new List<int>(){x};component[x]=nextId;
            for(int i=0;i<q.Count;i++) foreach(int y in adj[q[i]]) if(component[y]<0 && (col[y]==a || col[y]==b)) {component[y]=nextId;q.Add(y);}
            nextId++;
        }
        initial=new bool[m];rank=Enumerable.Repeat(-1,m).ToArray();int[] threshold=new int[m];
        for(int x=0;x<m;x++) if(col[x]!=a && col[x]!=b) {
            HashSet<int> ca=new HashSet<int>();foreach(int y in adj[x]) if(col[y]==a) ca.Add(component[y]);
            foreach(int y in adj[x]) if(col[y]==b && ca.Contains(component[y])) initial[x]=true;
            threshold[x]=2*(K-2)-adj[x].Count+adj[x].Count(y=>col[y]==a || col[y]==b);
        }
        bool[] keep=(bool[])initial.Clone();int number=0;bool changed=true;
        while(changed) {changed=false;for(int x=0;x<m;x++) if(keep[x] && adj[x].Count(y=>keep[y])<threshold[x]) {rank[x]=number++;keep[x]=false;changed=true;}}
        for(int x=0;x<m;x++) if(keep[x]) rank[x]=int.MaxValue;
    }
    static void ProtectedTrace(List<int[]> edges,List<int>[] adj,int[] original,string outputPath) {
        int h=Array.IndexOf(original,-1),chosenA=-1,chosenB=-1,bestRank=int.MaxValue;
        for(int a=0;a<K;a++) for(int b=a+1;b<K;b++) {
            bool[] initial;int[] rank,component;BuildCore(adj,original,a,b,out initial,out rank,out component);
            if(initial[h] && rank[h]<bestRank) {chosenA=a;chosenB=b;bestRank=rank[h];}
        }
        if(chosenA<0) {Console.WriteLine("no nontrivial protected trace");return;}
        bool[] allowed;int[] ranks,comps;BuildCore(adj,original,chosenA,chosenB,out allowed,out ranks,out comps);
        int[] col=(int[])original.Clone();List<string> actions=new List<string>();int moves=0,swaps=0;
        while(true) {
            int x=Array.IndexOf(col,-1);int[][] mult=Multiplicities(adj,col,false);
            int free=Array.FindIndex(mult[x],v=>v==0);
            if(free>=0) {col[x]=free;actions.Add("{\"type\":\"fill\",\"vertex\":"+x+",\"colour\":"+free+"}");break;}
            if(!allowed[x]) {
                HashSet<int> selected=new HashSet<int>(adj[x].Where(y=>col[y]==chosenA).Select(y=>comps[y]));
                int[] changed=Enumerable.Range(0,col.Length).Where(y=>comps[y]>=0 && selected.Contains(comps[y])).ToArray();
                foreach(int y in changed) col[y]=chosenA+chosenB-col[y];
                if(!Valid(adj,col) || adj[x].Any(y=>col[y]==chosenA)) throw new Exception("Kempe repair");
                swaps=selected.Count;actions.Add("{\"type\":\"kempe\",\"vertices\":["+string.Join(",",changed)+"]}");
                col[x]=chosenA;actions.Add("{\"type\":\"fill\",\"vertex\":"+x+",\"colour\":"+chosenA+"}");break;
            }
            List<int> options=adj[x].Where(y=>col[y]!=chosenA && col[y]!=chosenB && mult[x][col[y]]==1 && ranks[y]<ranks[x]).OrderByDescending(y=>ranks[y]).ToList();
            if(options.Count==0) throw new Exception("peeling progress");
            int target=options[0],colour=col[target];col[x]=colour;col[target]=-1;moves++;
            actions.Add("{\"type\":\"hole\",\"from\":"+x+",\"to\":"+target+",\"colour\":"+colour+"}");
            if(!Valid(adj,col)) throw new Exception("trace illegal");
        }
        if(col.Any(a=>a<0) || !Valid(adj,col)) throw new Exception("final trace invalid");
        string extra="\"protected_pair\":["+chosenA+","+chosenB+"],\n\"initial_hole_rank\":"+bestRank+",\n\"actions\":["+string.Join(",",actions)+"],\n\"final_colouring\":["+string.Join(",",col)+"]";
        File.WriteAllText(outputPath,JsonState(edges,original,extra));
        Console.WriteLine("protected_trace pair="+chosenA+","+chosenB+" initial_rank="+bestRank+" hole_moves="+moves+" swapped_components="+swaps+" verified_complete=true output="+outputPath);
    }
    static void FindTransport(List<int[]> edges,List<int>[] adj,int[] original,List<int>[] arcs,int[][] mult,string outputPath) {
        int h=Array.IndexOf(original,-1);
        for(int preference=0;preference<2;preference++) foreach(int x in arcs[h]) foreach(int g in arcs[x]) {
            if(g==h || (preference==0 && arcs[h].Contains(g))) continue;
            int[] after=(int[])original.Clone();after[h]=original[x];after[x]=original[g];after[g]=-1;
            if(!Valid(adj,after)) continue;
            int[][] changed=Multiplicities(adj,after,false);
            foreach(int f in arcs[g]) foreach(int w in arcs[f]) {
                if(w==g || adj[g].Contains(w) || !arcs[w].Contains(f) || f==h || f==x || w==h || w==x) continue;
                int a=original[f],b=original[w];
                if(changed[g][a]==1 && changed[w][a]==1 && changed[f][b]==1) continue;
                string extra="\"path\":["+h+","+x+","+g+"],\n\"shortest_static_path\":"+(!arcs[h].Contains(g)).ToString().ToLower()+",\n\"double\":["+g+","+f+","+w+"],\n\"double_colours\":["+a+","+b+"],\n\"after_path\":["+string.Join(",",after)+"],\n\"multiplicities_before\":["+mult[g][a]+","+mult[w][a]+","+mult[f][b]+"],\n\"multiplicities_after\":["+changed[g][a]+","+changed[w][a]+","+changed[f][b]+"]";
                File.WriteAllText(outputPath,JsonState(edges,original,extra));
                Console.WriteLine("transport_failure path="+h+","+x+","+g+" double="+g+","+f+","+w+" avoids_f_w=true before=1,1,1 after="+changed[g][a]+","+changed[w][a]+","+changed[f][b]+" output="+outputPath);return;
            }
        }
        Console.WriteLine("no length-two transport failure avoiding f,w found");
    }
}
