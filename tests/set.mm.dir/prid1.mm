include "cvv.mm"
include "wcel.mm"
include "cpr.mm"
include "prid1g.mm"
include "ax-mp.mm"

theorem prid1
  let cA: class A
  let cB: class B
  assume prid1.1: |- A e. _V


  assert |- A e. { A , B }

  proof
    cA
    cvv
    wcel
    cA
    cA
    cB
    cpr
    wcel
    prid1.1
    cA
    cB
    cvv
    prid1g
    ax-mp
end
