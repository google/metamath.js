include "cnr.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cmul.mm"
include "co.mm"
include "cmr.mm"
include "cm1r.mm"
include "cplr.mm"
include "cep.mm"
include "ccnv.mm"
include "cec.mm"
include "mulcnsr.mm"
include "opex.mm"
include "ecid.mm"
include "oveq12i.mm"
include "3eqtr4g.mm"

theorem mulcnsrec
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. R. /\ B e. R. ) /\ ( C e. R. /\ D e. R. ) ) -> ( [ <. A , B >. ] `' _E x. [ <. C , D >. ] `' _E ) = [ <. ( ( A .R C ) +R ( -1R .R ( B .R D ) ) ) , ( ( B .R C ) +R ( A .R D ) ) >. ] `' _E )

  proof
    cA
    cnr
    wcel
    cB
    cnr
    wcel
    wa
    cC
    cnr
    wcel
    cD
    cnr
    wcel
    wa
    wa
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    cmul
    co
    cA
    cC
    cmr
    co
    cm1r
    cB
    cD
    cmr
    co
    cmr
    co
    cplr
    co
    #
    cB
    cC
    cmr
    co
    cA
    cD
    cmr
    co
    cplr
    co
    #
    cop
    #
    @0
    cep
    ccnv
    #
    cec
    #
    @1
    @5
    cec
    #
    cmul
    co
    @4
    @5
    cec
    cA
    cB
    cC
    cD
    mulcnsr
    @6
    @0
    @7
    @1
    cmul
    @0
    cA
    cB
    opex
    ecid
    @1
    cC
    cD
    opex
    ecid
    oveq12i
    @4
    @2
    @3
    opex
    ecid
    3eqtr4g
end
