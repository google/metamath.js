include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cxne.mm"
include "cxad.mm"
include "cif.mm"
include "cxr.mm"
include "wceq.mm"
include "xmetcl.mm"
include "3adant3r2.mm"
include "3adant3r1.mm"
include "xrsdsval.mm"
include "syl2anc.mm"
include "3ancoma.mm"
include "xmetrtri.mm"
include "sylan2b.mm"
include "xmetsym.mm"
include "3adant3r3.mm"
include "breqtrrd.mm"
include "breq1.mm"
include "ifboth.mm"
include "eqbrtrd.mm"

theorem xmetrtri2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cK: class K
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vd: setvar d
  let vw: setvar w
  let cR: class R
  assume xmetrtri2.1: |- K = ( dist ` RR*s )


  assert |- ( ( D e. ( *Met ` X ) /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A D C ) K ( B D C ) ) <_ ( A D B ) )

  proof
    cD
    cX
    cxmt
    cfv
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
    cC
    cD
    co
    #
    cB
    cC
    cD
    co
    #
    cK
    co
    #
    @6
    @7
    cle
    wbr
    #
    @7
    @6
    cxne
    cxad
    co
    #
    @6
    @7
    cxne
    cxad
    co
    #
    cif
    #
    cA
    cB
    cD
    co
    #
    cle
    @5
    @6
    cxr
    wcel
    #
    @7
    cxr
    wcel
    #
    @8
    @12
    wceq
    @0
    @1
    @3
    @14
    @2
    cA
    cC
    cD
    cX
    xmetcl
    3adant3r2
    @0
    @2
    @3
    @15
    @1
    cB
    cC
    cD
    cX
    xmetcl
    3adant3r1
    @6
    @7
    cK
    xmetrtri2.1
    xrsdsval
    syl2anc
    @5
    @10
    @13
    cle
    wbr
    #
    @11
    @13
    cle
    wbr
    #
    @12
    @13
    cle
    wbr
    #
    @5
    @10
    cB
    cA
    cD
    co
    #
    @13
    cle
    @4
    @0
    @2
    @1
    @3
    w3a
    @10
    @19
    cle
    wbr
    @1
    @2
    @3
    3ancoma
    cB
    cA
    cC
    cD
    cX
    xmetrtri
    sylan2b
    @0
    @1
    @2
    @13
    @19
    wceq
    @3
    cA
    cB
    cD
    cX
    xmetsym
    3adant3r3
    breqtrrd
    cA
    cB
    cC
    cD
    cX
    xmetrtri
    @9
    @16
    @17
    @18
    @10
    @11
    @10
    @12
    @13
    cle
    breq1
    @11
    @12
    @13
    cle
    breq1
    ifboth
    syl2anc
    eqbrtrd
end
