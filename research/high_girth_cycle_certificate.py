"""Independent bad-list verifier: enumerate unordered two-color spoke sets.

No code from the original vertex-list search is imported.
"""
from itertools import combinations
from pathlib import Path
import json

def certify(group_lists,palette=255,save_details=False):
    n=len(group_lists)
    choices=[[sum(1<<c for c in pair) for pair in combinations([c for c in range(palette.bit_length()) if L>>c&1],2)]
             for L in group_lists]
    counts=dict(spoke_assignments=0,empty_cycle_list=0,clique_hall_failure=0,remaining_search_failure=0)
    details=[];witness=None
    def circle_color(lists):
        colors=[-1]*n
        def rec():
            uncolored=[v for v in range(n) if colors[v]<0]
            if not uncolored:return colors.copy()
            available={v:lists[v]&~sum(1<<c for c in set(colors[w] for w in range(n)
                                                  if colors[w]>=0 and min((v-w)%n,(w-v)%n)<=2))
                       for v in uncolored}
            v=min(uncolored,key=lambda v:available[v].bit_count())
            mask=available[v]
            while mask:
                b=mask&-mask;mask^=b;colors[v]=b.bit_length()-1
                answer=rec()
                if answer is not None:return answer
            colors[v]=-1
            return None
        return rec()
    def recurse(selected):
        nonlocal witness
        if witness:return
        i=len(selected)
        if i<n:
            for pair in choices[i]:
                if i and pair&selected[-1]:continue
                if i==n-1 and pair&selected[0]:continue
                recurse(selected+[pair])
            return
        counts['spoke_assignments']+=1
        lists=[palette&~(selected[(i-1)%n]|selected[i]|selected[(i+1)%n]|selected[(i+2)%n]) for i in range(n)]
        hall=None
        if not all(lists):counts['empty_cycle_list']+=1
        else:
            for size in range(2,n+1):
                for subset in combinations(range(n),size):
                    if not all(min((i-j)%n,(j-i)%n)<=2 for i,j in combinations(subset,2)):continue
                    union=0
                    for i in subset:union|=lists[i]
                    if union.bit_count()<size:
                        hall=list(subset);break
                if hall is not None:break
            if hall is not None:counts['clique_hall_failure']+=1
            else:
                answer=circle_color(lists)
                if answer is not None:witness=dict(spoke_sets=selected,cycle_coloring=answer)
                else:counts['remaining_search_failure']+=1
        if save_details:details.append(dict(spoke_sets=selected,cycle_lists=lists,clique_hall_failure=hall))
    recurse([])
    return dict(group_lists=group_lists,status='sat' if witness else 'unsat',counts=counts,witness=witness,details=details)

if __name__=='__main__':
    groups=[122,59,205,205,167,182]
    result=certify(groups,save_details=True)
    Path('research/high_girth_six_cycle_certificate.json').write_text(json.dumps(result,indent=2))
    print(result['status'],result['counts'])
