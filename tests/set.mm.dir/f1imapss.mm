include "wf1.mm"
include "wss.mm"
include "wa.mm"
include "cima.mm"
include "wceq.mm"
include "wn.mm"
include "wpss.mm"
include "f1imass.mm"
include "f1imaeq.mm"
include "notbid.mm"
include "anbi12d.mm"
include "dfpss2.mm"
include "3bitr4g.mm"

theorem f1imapss
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let va: setvar a


  assert |- ( ( F : A -1-1-> B /\ ( C C_ A /\ D C_ A ) ) -> ( ( F " C ) C. ( F " D ) <-> C C. D ) )

  proof
    cA
    cB
    cF
    wf1
    cC
    cA
    wss
    cD
    cA
    wss
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
    @1
    @2
    wceq
    #
    wn
    #
    wa
    cC
    cD
    wss
    #
    cC
    cD
    wceq
    #
    wn
    #
    wa
    @1
    @2
    wpss
    cC
    cD
    wpss
    @0
    @3
    @6
    @5
    @8
    cA
    cB
    cC
    cD
    cF
    f1imass
    @0
    @4
    @7
    cA
    cB
    cC
    cD
    cF
    f1imaeq
    notbid
    anbi12d
    @1
    @2
    dfpss2
    cC
    cD
    dfpss2
    3bitr4g
end
