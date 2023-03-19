include "cxp.mm"
include "wfn.mm"
include "wcel.mm"
include "co.mm"
include "crn.mm"
include "wa.mm"
include "cop.mm"
include "opelxpi.mm"
include "cfv.mm"
include "df-ov.mm"
include "fnfvelrn.mm"
include "syl5eqel.mm"
include "sylan2.mm"
include "3impb.mm"

theorem fnovrn
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F


  assert |- ( ( F Fn ( A X. B ) /\ C e. A /\ D e. B ) -> ( C F D ) e. ran F )

  proof
    cF
    cA
    cB
    cxp
    #
    wfn
    #
    cC
    cA
    wcel
    #
    cD
    cB
    wcel
    #
    cC
    cD
    cF
    co
    #
    cF
    crn
    #
    wcel
    #
    @2
    @3
    wa
    @1
    cC
    cD
    cop
    #
    @0
    wcel
    #
    @6
    cC
    cD
    cA
    cB
    opelxpi
    @1
    @8
    wa
    @4
    @7
    cF
    cfv
    @5
    cC
    cD
    cF
    df-ov
    @0
    @7
    cF
    fnfvelrn
    syl5eqel
    sylan2
    3impb
end
