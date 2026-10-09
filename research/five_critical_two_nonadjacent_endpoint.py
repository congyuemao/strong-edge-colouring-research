"""Girth-five endpoint realization showing why nonadjacent high points differ."""
import json
from pathlib import Path
from itertools import combinations
from small_clique_insertion_obstruction import adj, conflicts, girth_at_least_five, colour


def main():
    # 0,1,2 are the common triangle; 3,4 are nonadjacent high points;
    # 5..8 form the other K4, with pairs attached to high 3 and high 4.
    red = [(0,1),(1,2),(2,3),(4,5),(6,7),
           (8,10),(8,11),(9,12),(9,13),(14,15),
           (0,16),(17,18),(17,19)]
    blue = [(1,4),(3,5),(1,6),(3,7),(4,8),(6,9),(8,9),
            (0,14),(0,17)]
    ng = adj(20, red + blue)
    girth_at_least_five(ng)
    assert max(map(len, ng)) == 4
    assert max(map(len, adj(20, red))) == 2
    assert max(map(len, adj(20, blue))) == 2
    h = conflicts(ng, red)
    expected = set(combinations(range(3), 2))
    expected |= {(i,j) for i in range(3) for j in (3,4)}
    expected |= set(combinations(range(5,9), 2))
    expected |= {(3,5),(3,6),(4,7),(4,8)}
    actual = {(u,v) for u in range(9) for v in h[u] if u < v < 9}
    assert actual == expected
    assert [len(h[i] & set(range(9))) for i in range(9)] == [4,4,4,5,5,4,4,4,4]
    aa = set(range(1,10))
    bb = {0,10,11,12}
    assert all(v in h[u] for u,v in combinations(bb,2))
    assert h[0] & aa == {1,2,3,4,9}
    degrees_a = {v:len(h[v]&aa) for v in aa}
    assert max(degrees_a.values()) == 4
    assert {v for v in h[0]&aa if degrees_a[v] == 4} == {3,4}
    assert 4 not in h[3]
    assert not any(all(v in h[u] for u,v in combinations(q,2))
                   for q in combinations(aa | {0},5))
    four = colour(h,aa,4)
    assert four is not None
    assert colour(h,aa | {0},4) is None
    five = colour(h,aa | {0},5)
    assert five is not None
    deletions = [colour(h,set(range(9))-{v},4) for v in range(9)]
    assert all(c is not None for c in deletions)
    m = 4*20-2*(len(red)+len(blue))
    output = {"G_vertices":20,"red_edges":red,"blue_edges":blue,
              "A_indices":sorted(aa),"B_K4_indices":sorted(bb),"root":0,
              "root_A_neighbours":[1,2,3,4,9],
              "root_A_neighbours_of_A_degree_four":[3,4],
              "these_two_neighbours_are_adjacent":False,
              "nine_vertex_critical_edges":sorted(expected),
              "A_four_colouring":four,"A_plus_root_five_colouring":five,
              "critical_vertex_deletion_four_colourings":deletions,
              "finite_regular_completion_lemma":"two_factor_finite_completion.md",
              "completion_new_base_edges":m,
              "completion_vertex_count_bound":2*20*5**m,
              "scope":"Endpoint and finite existence certificate only; no globally optimal A/B/C partition asserted."}
    path=Path(__file__).with_suffix(".json")
    path.write_text(json.dumps(output,indent=2),encoding="utf-8")
    print(json.dumps({"core_vertices":20,"root_A_degree":5,
                      "critical_high_points":[3,4],"completion_exponent":m,
                      "output":str(path)},indent=2))


if __name__ == "__main__":
    main()
