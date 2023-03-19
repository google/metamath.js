include "wceq.mm"
include "csup.mm"
include "supeq1.mm"
include "ax-mp.mm"

theorem supeq1i
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume supeq1i.1: |- B = C


  assert |- sup ( B , A , R ) = sup ( C , A , R )

  proof
    cB
    cC
    wceq
    cB
    cA
    cR
    csup
    cC
    cA
    cR
    csup
    wceq
    supeq1i.1
    cA
    cB
    cC
    cR
    supeq1
    ax-mp
end
