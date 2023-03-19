include "cch.mm"
include "wcel.mm"
include "csh.mm"
include "csn.mm"
include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "chsh.mm"
include "sh1dle.mm"
include "sylan.mm"

theorem ch1dle
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. A ) -> ( _|_ ` ( _|_ ` { B } ) ) C_ A )

  proof
    cA
    cch
    wcel
    cA
    csh
    wcel
    cB
    cA
    wcel
    cB
    csn
    cort
    cfv
    cort
    cfv
    cA
    wss
    cA
    chsh
    cA
    cB
    sh1dle
    sylan
end
