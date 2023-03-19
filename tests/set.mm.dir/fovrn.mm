include "cxp.mm"
include "wf.mm"
include "wcel.mm"
include "co.mm"
include "wa.mm"
include "cop.mm"
include "opelxpi.mm"
include "cfv.mm"
include "df-ov.mm"
include "ffvelrn.mm"
include "syl5eqel.mm"
include "sylan2.mm"
include "3impb.mm"

theorem fovrn
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F


  assert |- ( ( F : ( R X. S ) --> C /\ A e. R /\ B e. S ) -> ( A F B ) e. C )

  proof
    cR
    cS
    cxp
    #
    cC
    cF
    wf
    #
    cA
    cR
    wcel
    #
    cB
    cS
    wcel
    #
    cA
    cB
    cF
    co
    #
    cC
    wcel
    #
    @2
    @3
    wa
    @1
    cA
    cB
    cop
    #
    @0
    wcel
    #
    @5
    cA
    cB
    cR
    cS
    opelxpi
    @1
    @7
    wa
    @4
    @6
    cF
    cfv
    cC
    cA
    cB
    cF
    df-ov
    @0
    cC
    @6
    cF
    ffvelrn
    syl5eqel
    sylan2
    3impb
end
