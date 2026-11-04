using System;
using System.Linq;
using System.Collections.Generic;

// This verifier deliberately builds L(G) first and then squares it, rather
// than using the endpoint-joining test used by the generator.
public class IndependentVerifier {
    readonly int n,m;
    readonly List<int>[] graph,line,conflict;
    readonly List<int[]> edges;
    public int[] Colours;
    public int Girth;
    public IndependentVerifier(List<int[]> inputEdges,int[] inputColours) {
        edges=inputEdges; m=edges.Count;n=edges.Max(e=>e.Max())+1;Colours=(int[])inputColours.Clone();
        if(Colours.Length!=m) throw new Exception("size mismatch");
        graph=Enumerable.Range(0,n).Select(x=>new List<int>()).ToArray();
        HashSet<string> unique=new HashSet<string>();
        foreach(int[] e in edges) {
            if(e.Length!=2 || e[0]==e[1] || !unique.Add(string.Join(",",e.OrderBy(x=>x)))) throw new Exception("not simple");
            graph[e[0]].Add(e[1]);graph[e[1]].Add(e[0]);
        }
        if(graph.Any(x=>x.Count!=4)) throw new Exception("not four regular");
        Girth=int.MaxValue;
        foreach(int[] removed in edges) {
            int source=removed[0],target=removed[1];int[] dist=Enumerable.Repeat(-1,n).ToArray();
            List<int> q=new List<int>(){source};dist[source]=0;
            for(int i=0;i<q.Count && dist[target]<0;i++) foreach(int y in graph[q[i]]) {
                int x=q[i];if((x==source && y==target) || (x==target && y==source)) continue;
                if(dist[y]<0) {dist[y]=dist[x]+1;q.Add(y);}
            }
            if(dist[target]>=0) Girth=Math.Min(Girth,dist[target]+1);
        }
        if(Girth<7) throw new Exception("girth too small");
        line=Enumerable.Range(0,m).Select(x=>new List<int>()).ToArray();
        for(int vertex=0;vertex<n;vertex++) {
            List<int> incident=Enumerable.Range(0,m).Where(i=>edges[i][0]==vertex || edges[i][1]==vertex).ToList();
            foreach(int x in incident) foreach(int y in incident) if(x!=y) line[x].Add(y);
        }
        conflict=new List<int>[m];
        for(int x=0;x<m;x++) {
            HashSet<int> ball=new HashSet<int>(line[x]);foreach(int y in line[x]) foreach(int z in line[y]) ball.Add(z);
            ball.Remove(x);conflict[x]=ball.ToList();
        }
        if(conflict.Any(x=>x.Count!=24)) throw new Exception("wrong conflict degree");
        CheckProper();if(Colours.Count(c=>c<0)!=1) throw new Exception("not one hole");
    }
    public void CheckProper() {
        for(int x=0;x<m;x++) {
            if(Colours[x]<-1 || Colours[x]>=20) throw new Exception("colour range");
            if(Colours[x]>=0 && conflict[x].Any(y=>Colours[y]==Colours[x])) throw new Exception("improper colouring");
        }
    }
    int[] Count(int x) {
        int[] count=new int[20];foreach(int y in conflict[x]) if(Colours[y]>=0) count[Colours[y]]++;return count;
    }
    public bool Blocked() {return Count(Array.IndexOf(Colours,-1)).All(x=>x>0);}
    public void Hole(int source,int target,int colour) {
        if(Colours[source]!=-1 || Colours[target]!=colour || !conflict[source].Contains(target) || Count(source)[colour]!=1) throw new Exception("illegal move");
        Colours[source]=colour;Colours[target]=-1;CheckProper();
    }
    public void Fill(int x,int colour) {
        if(Colours[x]!=-1 || Count(x)[colour]!=0) throw new Exception("illegal fill");Colours[x]=colour;CheckProper();
    }
    public void Kempe(int[] vertices,int a,int b) {
        HashSet<int> selected=new HashSet<int>(vertices);
        foreach(int x in selected) {
            if(Colours[x]!=a && Colours[x]!=b) throw new Exception("wrong Kempe colours");
            if(conflict[x].Any(y=>(Colours[y]==a || Colours[y]==b) && !selected.Contains(y))) throw new Exception("incomplete Kempe component");
        }
        foreach(int x in selected) Colours[x]=a+b-Colours[x];CheckProper();
    }
    public void Expected(int[] wanted) {if(!Colours.SequenceEqual(wanted)) throw new Exception("state mismatch");}
    public bool Double(int g,int f,int w) {
        if(g==f || g==w || f==w || Colours[f]<0 || Colours[w]<0 || !conflict[g].Contains(f) || !conflict[f].Contains(w) || conflict[g].Contains(w)) return false;
        int a=Colours[f],b=Colours[w];return Count(g)[a]==1 && Count(w)[a]==1 && Count(f)[b]==1;
    }
    public int StaticDistance(int source,int target) {
        int[] dist=Enumerable.Repeat(-1,m).ToArray();List<int> q=new List<int>(){source};dist[source]=0;
        for(int i=0;i<q.Count;i++) {
            int x=q[i];int[] count=Count(x);
            foreach(int y in conflict[x]) if(Colours[y]>=0 && count[Colours[y]]==1 && dist[y]<0) {dist[y]=dist[x]+1;q.Add(y);}
        }
        return dist[target];
    }
    public int MinimumHoleDepthTwo() {
        int[] original=(int[])Colours.Clone();int h=Array.IndexOf(Colours,-1);
        if(!Blocked()) return 0;
        int[] ch=Count(h);List<int> choices=conflict[h].Where(y=>ch[Colours[y]]==1).ToList();
        foreach(int x in choices) {
            Colours=(int[])original.Clone();Hole(h,x,Colours[x]);if(!Blocked()) {Colours=original;return 1;}
        }
        foreach(int x in choices) {
            Colours=(int[])original.Clone();Hole(h,x,Colours[x]);int[] first=(int[])Colours.Clone(),cx=Count(x);
            foreach(int y in conflict[x].Where(v=>cx[Colours[v]]==1).ToArray()) {
                Colours=(int[])first.Clone();Hole(x,y,Colours[y]);if(!Blocked()) {Colours=original;return 2;}
            }
        }
        Colours=original;return -1;
    }
    public int[] Core(int a,int b) {
        int[] id=Enumerable.Repeat(-1,m).ToArray();int index=0;
        for(int root=0;root<m;root++) if(id[root]<0 && (Colours[root]==a || Colours[root]==b)) {
            List<int> q=new List<int>(){root};id[root]=index++;
            for(int i=0;i<q.Count;i++) foreach(int y in conflict[q[i]]) if(id[y]<0 && (Colours[y]==a || Colours[y]==b)) {id[y]=id[root];q.Add(y);}
        }
        HashSet<int> core=new HashSet<int>();int[] threshold=new int[m];
        for(int x=0;x<m;x++) if(Colours[x]!=a && Colours[x]!=b) {
            bool common=false;
            foreach(int y in conflict[x]) if(Colours[y]==a) foreach(int z in conflict[x]) if(Colours[z]==b && id[y]==id[z]) common=true;
            if(common) core.Add(x);
            threshold[x]=36-conflict[x].Count+conflict[x].Count(y=>Colours[y]==a || Colours[y]==b);
        }
        bool repeat=true;
        while(repeat) {
            List<int> batch=core.Where(x=>conflict[x].Count(y=>core.Contains(y))<threshold[x]).ToList();
            repeat=batch.Count>0;foreach(int x in batch) core.Remove(x);
        }
        return core.OrderBy(x=>x).ToArray();
    }
    public string PairSummary() {
        int hole=Array.IndexOf(Colours,-1),repair=0,min=m,max=0;
        for(int a=0;a<20;a++) for(int b=a+1;b<20;b++) {int[] core=Core(a,b);if(!core.Contains(hole)) repair++;min=Math.Min(min,core.Length);max=Math.Max(max,core.Length);}
        return "repair_pairs="+repair+" min_core="+min+" max_core="+max;
    }
    public void PairedConstruction(int centres) {
        if(n!=5*centres) throw new Exception("paired vertex count");
        for(int c=0;c<centres;c++) {
            int[] expected=new int[]{centres+2*c,centres+2*c+1,3*centres+2*c,3*centres+2*c+1};
            if(!graph[c].OrderBy(x=>x).SequenceEqual(expected.OrderBy(x=>x))) throw new Exception("paired star");
        }
        foreach(int[] e in edges) if(e[0]>=centres && !((e[0]<3*centres && e[1]>=3*centres) || (e[1]<3*centres && e[0]>=3*centres))) throw new Exception("wrong bipartite remainder");
        int[] fixedVertices=Enumerable.Range(0,m).Where(x=>Colours[x]==0 || Colours[x]==1).ToArray();
        if(fixedVertices.Length!=2*centres) throw new Exception("fixed class size");
        foreach(int x in fixedVertices) {
            if(edges[x][0]>=centres || edges[x][1]<centres || edges[x][1]>=3*centres || Colours[x]!=(edges[x][1]-centres)%2) throw new Exception("fixed colour placement");
            if(conflict[x].Count(y=>Colours[y]==0 || Colours[y]==1)!=1) throw new Exception("component not pair");
        }
        int[] core=Core(0,1);
        if(core.Length!=8*centres || core.Any(x=>Colours[x]==0 || Colours[x]==1)) throw new Exception("paired core wrong");
    }
}
