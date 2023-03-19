include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cxp.mm"
include "cr.mm"
include "wf.mm"
include "cme.mm"
include "cxr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "rpxr.mm"
include "rpgt0.mm"
include "jca.mm"
include "stdbdxmet.mm"
include "3expb.mm"
include "sylan2.mm"
include "cv.mm"
include "co.mm"
include "cle.mm"
include "cif.mm"
include "wral.mm"
include "xmetcl.mm"
include "adantlr.mm"
include "ad2antlr.mm"
include "ifcld.mm"
include "rpre.mm"
include "xmetge0.mm"
include "rpge0.mm"
include "breq2.mm"
include "ifboth.mm"
include "syl2anc.mm"
include "xrmin2.mm"
include "xrrege0.mm"
include "syl22anc.mm"
include "ralrimivva.mm"
include "fmpt2.mm"
include "sylib.mm"
include "ismet2.mm"
include "sylanbrc.mm"

theorem stdbdmet
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let cR: class R
  let cX: class X
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let vr: setvar r
  let vs: setvar s
  let vz: setvar z
  let cJ: class J
  let cS: class S
  let cB: class B
  let cP: class P
  assume stdbdmet.1: |- D = ( x e. X , y e. X |-> if ( ( x C y ) <_ R , ( x C y ) , R ) )

  disjoint x y
  disjoint C x
  disjoint C y
  disjoint R x
  disjoint R y
  disjoint X x
  disjoint X y
  disjoint A x
  disjoint A y
  disjoint a b
  disjoint a r
  disjoint a s
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint C a
  disjoint b r
  disjoint b s
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint C b
  disjoint r s
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint C r
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint C s
  disjoint x z
  disjoint y z
  disjoint C z
  disjoint D r
  disjoint D s
  disjoint D z
  disjoint J r
  disjoint J s
  disjoint J z
  disjoint S z
  disjoint B x
  disjoint B y
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint R a
  disjoint R b
  disjoint R r
  disjoint R s
  disjoint R z
  disjoint X a
  disjoint X b
  disjoint X r
  disjoint X s
  disjoint X z
  assert |- ( ( C e. ( *Met ` X ) /\ R e. RR+ ) -> D e. ( Met ` X ) )

  proof
    cC
    cX
    cxmt
    cfv
    #
    wcel
    #
    cR
    crp
    wcel
    #
    wa
    #
    cD
    @0
    wcel
    #
    cX
    cX
    cxp
    cr
    cD
    wf
    #
    cD
    cX
    cme
    cfv
    wcel
    @2
    @1
    cR
    cxr
    wcel
    #
    cc0
    cR
    clt
    wbr
    #
    wa
    @4
    @2
    @6
    @7
    cR
    rpxr
    #
    cR
    rpgt0
    jca
    @1
    @6
    @7
    @4
    vx
    vy
    cC
    cD
    cR
    cX
    stdbdmet.1
    stdbdxmet
    3expb
    sylan2
    @3
    vx
    cv
    #
    vy
    cv
    #
    cC
    co
    #
    cR
    cle
    wbr
    #
    @11
    cR
    cif
    #
    cr
    wcel
    #
    vy
    cX
    wral
    vx
    cX
    wral
    @5
    @3
    @14
    vx
    vy
    cX
    cX
    @3
    @9
    cX
    wcel
    #
    @10
    cX
    wcel
    #
    wa
    #
    wa
    #
    @13
    cxr
    wcel
    cR
    cr
    wcel
    #
    cc0
    @13
    cle
    wbr
    #
    @13
    cR
    cle
    wbr
    #
    @14
    @18
    @12
    @11
    cR
    cxr
    @1
    @17
    @11
    cxr
    wcel
    #
    @2
    @1
    @15
    @16
    @22
    @9
    @10
    cC
    cX
    xmetcl
    3expb
    adantlr
    #
    @2
    @6
    @1
    @17
    @8
    ad2antlr
    #
    ifcld
    @2
    @19
    @1
    @17
    cR
    rpre
    ad2antlr
    @18
    cc0
    @11
    cle
    wbr
    #
    cc0
    cR
    cle
    wbr
    #
    @20
    @1
    @17
    @25
    @2
    @1
    @15
    @16
    @25
    @9
    @10
    cC
    cX
    xmetge0
    3expb
    adantlr
    @2
    @26
    @1
    @17
    cR
    rpge0
    ad2antlr
    @12
    @25
    @26
    @20
    @11
    cR
    @11
    @13
    cc0
    cle
    breq2
    cR
    @13
    cc0
    cle
    breq2
    ifboth
    syl2anc
    @18
    @22
    @6
    @21
    @23
    @24
    @11
    cR
    xrmin2
    syl2anc
    @13
    cR
    xrrege0
    syl22anc
    ralrimivva
    vx
    vy
    cX
    cX
    @13
    cr
    cD
    stdbdmet.1
    fmpt2
    sylib
    cD
    cX
    ismet2
    sylanbrc
end
