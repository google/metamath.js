include "ccring.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "crngocom.mm"
include "3adant3r1.mm"
include "oveq2d.mm"
include "crngo.mm"
include "crngorngo.mm"
include "rngoass.mm"
include "sylan.mm"
include "3exp2.mm"
include "com34.mm"
include "3imp2.mm"
include "3eqtr4d.mm"

theorem crngm23
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cG: class G
  let cH: class H
  let cX: class X
  assume crngm.1: |- G = ( 1st ` R )
  assume crngm.2: |- H = ( 2nd ` R )
  assume crngm.3: |- X = ran G


  assert |- ( ( R e. CRingOps /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A H B ) H C ) = ( ( A H C ) H B ) )

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
    cC
    cX
    wcel
    #
    w3a
    #
    wa
    #
    cA
    cB
    cC
    cH
    co
    #
    cH
    co
    #
    cA
    cC
    cB
    cH
    co
    #
    cH
    co
    #
    cA
    cB
    cH
    co
    cC
    cH
    co
    #
    cA
    cC
    cH
    co
    cB
    cH
    co
    #
    @5
    @6
    @8
    cA
    cH
    @0
    @2
    @3
    @6
    @8
    wceq
    @1
    cB
    cC
    cR
    cG
    cH
    cX
    crngm.1
    crngm.2
    crngm.3
    crngocom
    3adant3r1
    oveq2d
    @0
    cR
    crngo
    wcel
    #
    @4
    @10
    @7
    wceq
    cR
    crngorngo
    #
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
    rngoass
    sylan
    @0
    @12
    @4
    @11
    @9
    wceq
    #
    @13
    @12
    @1
    @2
    @3
    @14
    @12
    @1
    @3
    @2
    @14
    @12
    @1
    @3
    @2
    @14
    cA
    cC
    cB
    cR
    cG
    cH
    cX
    crngm.1
    crngm.2
    crngm.3
    rngoass
    3exp2
    com34
    3imp2
    sylan
    3eqtr4d
end
