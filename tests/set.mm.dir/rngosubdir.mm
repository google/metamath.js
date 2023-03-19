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
include "3adant3r3.mm"
include "oveq1d.mm"
include "rngocl.mm"
include "3adant3r2.mm"
include "3adant3r1.mm"
include "jca.mm"
include "3expb.mm"
include "syldan.mm"
include "idd.mm"
include "rngonegcl.mm"
include "ex.mm"
include "3anim123d.mm"
include "imp.mm"
include "rngodir.mm"
include "rngoneglmul.mm"
include "oveq2d.mm"
include "eqtr4d.mm"

theorem rngosubdir
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


  assert |- ( ( R e. RingOps /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A D B ) H C ) = ( ( A H C ) D ( B H C ) ) )

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
    cD
    co
    #
    cC
    cH
    co
    cA
    cB
    cG
    cgn
    cfv
    #
    cfv
    #
    cG
    co
    #
    cC
    cH
    co
    #
    cA
    cC
    cH
    co
    #
    cB
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
    cC
    cH
    @0
    @1
    @2
    @6
    @9
    wceq
    @3
    cA
    cB
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
    3adant3r3
    oveq1d
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
    @3
    @17
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
    @0
    @2
    @3
    @18
    @1
    cB
    cC
    cR
    cG
    cH
    cX
    ringsubdi.1
    ringsubdi.2
    ringsubdi.3
    rngocl
    3adant3r1
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
    @8
    cC
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
    @8
    cX
    wcel
    #
    @3
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
    @22
    @3
    @3
    @0
    @1
    idd
    @0
    @2
    @22
    cB
    cR
    cG
    @7
    cX
    ringsubdi.1
    ringsubdi.3
    @14
    rngonegcl
    ex
    @0
    @3
    idd
    3anim123d
    imp
    cA
    @8
    cC
    cR
    cG
    cH
    cX
    ringsubdi.1
    ringsubdi.2
    ringsubdi.3
    rngodir
    syldan
    @5
    @15
    @20
    @11
    cG
    @0
    @2
    @3
    @15
    @20
    wceq
    @1
    cB
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
    rngoneglmul
    3adant3r1
    oveq2d
    eqtr4d
    eqtr4d
    eqtr4d
end
