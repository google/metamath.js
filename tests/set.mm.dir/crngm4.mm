include "ccring.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "df-3an.mm"
include "crngm23.mm"
include "sylan2br.mm"
include "adantrrr.mm"
include "oveq1d.mm"
include "crngo.mm"
include "crngorngo.mm"
include "rngocl.mm"
include "3expb.mm"
include "adantrr.mm"
include "simprrl.mm"
include "simprrr.mm"
include "3jca.mm"
include "rngoass.mm"
include "syldan.mm"
include "sylan.mm"
include "adantrlr.mm"
include "simprlr.mm"
include "3eqtr3d.mm"
include "3impb.mm"

theorem crngm4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cG: class G
  let cH: class H
  let cX: class X
  assume crngm.1: |- G = ( 1st ` R )
  assume crngm.2: |- H = ( 2nd ` R )
  assume crngm.3: |- X = ran G


  assert |- ( ( R e. CRingOps /\ ( A e. X /\ B e. X ) /\ ( C e. X /\ D e. X ) ) -> ( ( A H B ) H ( C H D ) ) = ( ( A H C ) H ( B H D ) ) )

  proof
    cR
    ccring
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    wa
    #
    cC
    cX
    wcel
    #
    cD
    cX
    wcel
    #
    wa
    #
    cA
    cB
    cH
    co
    #
    cC
    cD
    cH
    co
    cH
    co
    #
    cA
    cC
    cH
    co
    #
    cB
    cD
    cH
    co
    cH
    co
    #
    wceq
    @0
    @3
    @6
    wa
    #
    wa
    #
    @7
    cC
    cH
    co
    #
    cD
    cH
    co
    #
    @9
    cB
    cH
    co
    #
    cD
    cH
    co
    #
    @8
    @10
    @12
    @13
    @15
    cD
    cH
    @0
    @3
    @4
    @13
    @15
    wceq
    #
    @5
    @3
    @4
    wa
    @0
    @1
    @2
    @4
    w3a
    @17
    @1
    @2
    @4
    df-3an
    cA
    cB
    cC
    cR
    cG
    cH
    cX
    crngm.1
    crngm.2
    crngm.3
    crngm23
    sylan2br
    adantrrr
    oveq1d
    @0
    cR
    crngo
    wcel
    #
    @11
    @14
    @8
    wceq
    #
    cR
    crngorngo
    #
    @18
    @11
    @7
    cX
    wcel
    #
    @4
    @5
    w3a
    @19
    @18
    @11
    wa
    #
    @21
    @4
    @5
    @18
    @3
    @21
    @6
    @18
    @1
    @2
    @21
    cA
    cB
    cR
    cG
    cH
    cX
    crngm.1
    crngm.2
    crngm.3
    rngocl
    3expb
    adantrr
    @18
    @3
    @4
    @5
    simprrl
    @18
    @3
    @4
    @5
    simprrr
    #
    3jca
    @7
    cC
    cD
    cR
    cG
    cH
    cX
    crngm.1
    crngm.2
    crngm.3
    rngoass
    syldan
    sylan
    @0
    @18
    @11
    @16
    @10
    wceq
    #
    @20
    @18
    @11
    @9
    cX
    wcel
    #
    @2
    @5
    w3a
    @24
    @22
    @25
    @2
    @5
    @18
    @3
    @4
    @25
    @5
    @18
    @1
    @4
    @25
    @2
    @18
    @1
    @4
    @25
    cA
    cC
    cR
    cG
    cH
    cX
    crngm.1
    crngm.2
    crngm.3
    rngocl
    3expb
    adantrlr
    adantrrr
    @18
    @1
    @2
    @6
    simprlr
    @23
    3jca
    @9
    cB
    cD
    cR
    cG
    cH
    cX
    crngm.1
    crngm.2
    crngm.3
    rngoass
    syldan
    sylan
    3eqtr3d
    3impb
end
