include "wcel.mm"
include "wa.mm"
include "cplusr.mm"
include "co.mm"
include "cr.mm"
include "wfn.mm"
include "wceq.mm"
include "addrfn.mm"
include "ancoms.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "w3a.mm"
include "caddc.mm"
include "addcomgi.mm"
include "addrfv.mm"
include "3com12.mm"
include "3eqtr4a.mm"
include "3expia.mm"
include "ralrimiv.mm"
include "eqfnfv.mm"
include "syl5ibrcom.mm"
include "mp2and.mm"

theorem addrcom
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x


  assert |- ( ( A e. C /\ B e. D ) -> ( A +r B ) = ( B +r A ) )

  proof
    cA
    cC
    wcel
    #
    cB
    cD
    wcel
    #
    wa
    #
    cA
    cB
    cplusr
    co
    #
    cr
    wfn
    #
    cB
    cA
    cplusr
    co
    #
    cr
    wfn
    #
    @3
    @5
    wceq
    #
    cA
    cB
    cC
    cD
    addrfn
    @1
    @0
    @6
    cB
    cA
    cD
    cC
    addrfn
    ancoms
    @2
    @7
    @4
    @6
    wa
    vx
    cv
    #
    @3
    cfv
    #
    @8
    @5
    cfv
    #
    wceq
    #
    vx
    cr
    wral
    @2
    @11
    vx
    cr
    @0
    @1
    @8
    cr
    wcel
    #
    @11
    @0
    @1
    @12
    w3a
    @8
    cA
    cfv
    #
    @8
    cB
    cfv
    #
    caddc
    co
    @14
    @13
    caddc
    co
    #
    @9
    @10
    @13
    @14
    addcomgi
    cA
    cB
    @8
    cD
    cC
    addrfv
    @1
    @0
    @12
    @10
    @15
    wceq
    cB
    cA
    @8
    cC
    cD
    addrfv
    3com12
    3eqtr4a
    3expia
    ralrimiv
    vx
    cr
    @3
    @5
    eqfnfv
    syl5ibrcom
    mp2and
end
