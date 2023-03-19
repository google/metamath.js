include "wf1.mm"
include "wss.mm"
include "wa.mm"
include "cima.mm"
include "wceq.mm"
include "f1imass.mm"
include "wb.mm"
include "ancom2s.mm"
include "anbi12d.mm"
include "eqss.mm"
include "3bitr4g.mm"

theorem f1imaeq
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let va: setvar a


  assert |- ( ( F : A -1-1-> B /\ ( C C_ A /\ D C_ A ) ) -> ( ( F " C ) = ( F " D ) <-> C = D ) )

  proof
    cA
    cB
    cF
    wf1
    #
    cC
    cA
    wss
    #
    cD
    cA
    wss
    #
    wa
    wa
    #
    cF
    cC
    cima
    #
    cF
    cD
    cima
    #
    wss
    #
    @5
    @4
    wss
    #
    wa
    cC
    cD
    wss
    #
    cD
    cC
    wss
    #
    wa
    @4
    @5
    wceq
    cC
    cD
    wceq
    @3
    @6
    @8
    @7
    @9
    cA
    cB
    cC
    cD
    cF
    f1imass
    @0
    @2
    @1
    @7
    @9
    wb
    cA
    cB
    cD
    cC
    cF
    f1imass
    ancom2s
    anbi12d
    @4
    @5
    eqss
    cC
    cD
    eqss
    3bitr4g
end
