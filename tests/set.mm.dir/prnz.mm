include "cpr.mm"
include "prid1.mm"
include "ne0ii.mm"

theorem prnz
  let cA: class A
  let cB: class B
  assume prnz.1: |- A e. _V


  assert |- { A , B } =/= (/)

  proof
    cA
    cA
    cB
    cpr
    cA
    cB
    prnz.1
    prid1
    ne0ii
end
