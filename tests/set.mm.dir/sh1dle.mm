include "csh.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cort.mm"
include "cfv.mm"
include "cspn.mm"
include "chil.mm"
include "wceq.mm"
include "shel.mm"
include "spansn.mm"
include "syl.mm"
include "spansnss.mm"
include "eqsstr3d.mm"

theorem sh1dle
  let cA: class A
  let cB: class B


  assert |- ( ( A e. SH /\ B e. A ) -> ( _|_ ` ( _|_ ` { B } ) ) C_ A )

  proof
    cA
    csh
    wcel
    cB
    cA
    wcel
    wa
    #
    cB
    csn
    #
    cort
    cfv
    cort
    cfv
    #
    @1
    cspn
    cfv
    #
    cA
    @0
    cB
    chil
    wcel
    @3
    @2
    wceq
    cB
    cA
    shel
    cB
    spansn
    syl
    cA
    cB
    spansnss
    eqsstr3d
end
