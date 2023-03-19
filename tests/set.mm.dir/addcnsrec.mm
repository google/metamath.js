include "cnr.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "caddc.mm"
include "co.mm"
include "cplr.mm"
include "cep.mm"
include "ccnv.mm"
include "cec.mm"
include "addcnsr.mm"
include "opex.mm"
include "ecid.mm"
include "oveq12i.mm"
include "3eqtr4g.mm"

theorem addcnsrec
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. R. /\ B e. R. ) /\ ( C e. R. /\ D e. R. ) ) -> ( [ <. A , B >. ] `' _E + [ <. C , D >. ] `' _E ) = [ <. ( A +R C ) , ( B +R D ) >. ] `' _E )

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
    caddc
    co
    cA
    cC
    cplr
    co
    #
    cB
    cD
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
    caddc
    co
    @4
    @5
    cec
    cA
    cB
    cC
    cD
    addcnsr
    @6
    @0
    @7
    @1
    caddc
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
