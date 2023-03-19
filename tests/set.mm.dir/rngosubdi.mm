include "crngo.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cgn.mm"
include "cfv.mm"
include "wceq.mm"
include "eqid.mm"
include "rngosub.mm"
include "3adant3r1.mm"
include "oveq2d.mm"
include "rngocl.mm"
include "3adant3r3.mm"
include "3adant3r2.mm"
include "jca.mm"
include "3expb.mm"
include "syldan.mm"
include "idd.mm"
include "rngonegcl.mm"
include "ex.mm"
include "3anim123d.mm"
include "imp.mm"
include "rngodi.mm"
include "rngonegrmul.mm"
include "eqtr4d.mm"

theorem rngosubdi
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cG: class G
  let cH: class H
  let cX: class X
  assume ringsubdi.1: |- G = ( 1st ` R )
  assume ringsubdi.2: |- H = ( 2nd ` R )
  assume ringsubdi.3: |- X = ran G
  assume ringsubdi.4: |- D = ( /g ` G )


  assert |- ( ( R e. RingOps /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( A H ( B D C ) ) = ( ( A H B ) D ( A H C ) ) )

  proof
    cR
    crngo
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
    cD
    co
    #
    cH
    co
    cA
    cB
    cC
    cG
    cgn
    cfv
    #
    cfv
    #
    cG
    co
    #
    cH
    co
    #
    cA
    cB
    cH
    co
    #
    cA
    cC
    cH
    co
    #
    cD
    co
    #
    @5
    @6
    @9
    cA
    cH
    @0
    @2
    @3
    @6
    @9
    wceq
    @1
    cB
    cC
    cD
    cR
    cG
    @7
    cX
    ringsubdi.1
    ringsubdi.3
    @7
    eqid
    #
    ringsubdi.4
    rngosub
    3adant3r1
    oveq2d
    @5
    @13
    @11
    @12
    @7
    cfv
    #
    cG
    co
    #
    @10
    @0
    @4
    @11
    cX
    wcel
    #
    @12
    cX
    wcel
    #
    wa
    @13
    @16
    wceq
    #
    @5
    @17
    @18
    @0
    @1
    @2
    @17
    @3
    cA
    cB
    cR
    cG
    cH
    cX
    ringsubdi.1
    ringsubdi.2
    ringsubdi.3
    rngocl
    3adant3r3
    @0
    @1
    @3
    @18
    @2
    cA
    cC
    cR
    cG
    cH
    cX
    ringsubdi.1
    ringsubdi.2
    ringsubdi.3
    rngocl
    3adant3r2
    jca
    @0
    @17
    @18
    @19
    @11
    @12
    cD
    cR
    cG
    @7
    cX
    ringsubdi.1
    ringsubdi.3
    @14
    ringsubdi.4
    rngosub
    3expb
    syldan
    @5
    @10
    @11
    cA
    @8
    cH
    co
    #
    cG
    co
    #
    @16
    @0
    @4
    @1
    @2
    @8
    cX
    wcel
    #
    w3a
    #
    @10
    @21
    wceq
    @0
    @4
    @23
    @0
    @1
    @1
    @2
    @2
    @3
    @22
    @0
    @1
    idd
    @0
    @2
    idd
    @0
    @3
    @22
    cC
    cR
    cG
    @7
    cX
    ringsubdi.1
    ringsubdi.3
    @14
    rngonegcl
    ex
    3anim123d
    imp
    cA
    cB
    @8
    cR
    cG
    cH
    cX
    ringsubdi.1
    ringsubdi.2
    ringsubdi.3
    rngodi
    syldan
    @5
    @15
    @20
    @11
    cG
    @0
    @1
    @3
    @15
    @20
    wceq
    @2
    cA
    cC
    cR
    cG
    cH
    @7
    cX
    ringsubdi.1
    ringsubdi.2
    ringsubdi.3
    @14
    rngonegrmul
    3adant3r2
    oveq2d
    eqtr4d
    eqtr4d
    eqtr4d
end
