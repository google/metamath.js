include "con0.mm"
include "limon.mm"
include "c1o.mm"
include "cvv.mm"
include "cv.mm"
include "comu.mm"
include "co.mm"
include "cmpt.mm"
include "rdgsuc.mm"
include "oesuclem.mm"

theorem oesuc
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. On /\ B e. On ) -> ( A ^o suc B ) = ( ( A ^o B ) .o A ) )

  proof
    vx
    cA
    cB
    con0
    limon
    c1o
    cB
    vx
    cvv
    vx
    cv
    cA
    comu
    co
    cmpt
    rdgsuc
    oesuclem
end
