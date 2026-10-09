"""Independent certificate validator: no solver code is imported."""
from pathlib import Path
from itertools import combinations
import json

def read(name):return json.loads(Path('research/'+name).read_text())

def conflict_pairs(n,edges):
    adjacency=[set() for _ in range(n)]
    assert len({tuple(e) for e in edges})==len(edges)
    for u,v in edges:
        assert u<v
        adjacency[u].add(v);adjacency[v].add(u)
    assert max(map(len,adjacency))<=4
    return [(i,j) for i,j in combinations(range(len(edges)),2)
            if set(edges[i])&set(edges[j]) or
               any(y in adjacency[x] for x in edges[i] for y in edges[j])]

def check_coloring(n,edges,colors,bound):
    pairs=conflict_pairs(n,edges)
    assert len(colors)==len(edges) and min(colors)>=0 and max(colors)<bound
    assert all(colors[i]!=colors[j] for i,j in pairs)
    return pairs

def partitions_by_sequential_assignment(n,pairs):
    neighbors=[set() for _ in range(n)]
    for i,j in pairs:neighbors[i].add(j);neighbors[j].add(i)
    answer=set();assignment=[]
    def visit(used):
        v=len(assignment)
        if v==n:answer.add(tuple(assignment));return
        forbidden={assignment[w] for w in neighbors[v] if w<v}
        for c in range(used+1):
            if c not in forbidden:
                assignment.append(c);visit(max(used,c+1));assignment.pop()
    visit(0)
    return answer

def reconstruct(blocks,record):
    edges={(10*i+u,10*i+v) for i,b in enumerate(record['block_indices'])
           for u,v in blocks[b]['surviving_edges']}
    edges|={tuple(e) for e in record['connections']}
    return 10*len(record['block_indices']),sorted(edges)

def run():
    blocks=read('gadget_block_signatures.json')
    signatures=0
    for b in blocks:
        es=b['surviving_edges'];k=b['chromatic_number']
        pairs=check_coloring(10,es,b['minimum_coloring'],k)
        assert len(b['maximum_clique'])==k
        pairset=set(pairs)
        assert all(tuple(sorted((u,v))) in pairset for u,v in combinations(b['maximum_clique'],2))
        declared={tuple(c) for c in b['all_color_partitions']}
        assert declared==partitions_by_sequential_assignment(len(es),pairs)
        assert len(declared)==b['total_partitions']
        signatures+=len(declared)
    glues=read('gadget_two_block_gluings.json')['records']
    for g in glues:
        n,es=reconstruct(blocks,g)
        assert len(es)==40
        check_coloring(n,es,g['coloring'],19)
    randoms=read('gadget_random_gluings.json')['records']
    improved=read('gadget_worst_case_19.json')
    for i,g in enumerate(randoms):
        n,es=reconstruct(blocks,g)
        colors=g['coloring']
        if i==improved['random_record_index']:
            assert es==[tuple(e) for e in improved['edges']]
            colors=improved['result']['coloring']
        check_coloring(n,es,colors,19)
    print('validated',len(blocks),'deletion orbits;',signatures,'complete color signatures;',
          len(glues),'exhaustive two-block gluings and',len(randoms),'random gluings, all <=19 colors')

if __name__=='__main__':run()
