include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "crp.mm"
include "wral.mm"
include "cc0.mm"
include "rpge0.mm"
include "adantl.mm"
include "simplr.mm"
include "rpre.mm"
include "addge01d.mm"
include "mpbid.mm"
include "wi.mm"
include "simpll.mm"
include "rexrd.mm"
include "readdcld.mm"
include "xrletr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "ralrimdva.mm"
include "clt.mm"
include "wn.mm"
include "cq.mm"
include "wrex.mm"
include "rexr.mm"
include "simpl.mm"
include "qbtwnxr.mm"
include "3expia.mm"
include "syl2anc.mm"
include "cmin.mm"
include "simprrl.mm"
include "wb.mm"
include "qre.mm"
include "ad2antrl.mm"
include "difrp.mm"
include "simprrr.mm"
include "xrltnle.mm"
include "recnd.mm"
include "pncan3d.mm"
include "breq2d.mm"
include "mtbird.mm"
include "wceq.mm"
include "oveq2.mm"
include "notbid.mm"
include "rspcev.mm"
include "rexnal.mm"
include "sylib.mm"
include "rexlimdvaa.mm"
include "syld.mm"
include "con2d.mm"
include "xrlenlt.mm"
include "sylan2.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem xralrple
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( ( A e. RR* /\ B e. RR ) -> ( A <_ B <-> A. x e. RR+ A <_ ( B + x ) ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    cB
    cle
    wbr
    #
    cA
    cB
    vx
    cv
    #
    caddc
    co
    #
    cle
    wbr
    #
    vx
    crp
    wral
    #
    @2
    @3
    @6
    vx
    crp
    @2
    @4
    crp
    wcel
    #
    wa
    #
    @3
    cB
    @5
    cle
    wbr
    #
    @6
    @9
    cc0
    @4
    cle
    wbr
    #
    @10
    @8
    @11
    @2
    @4
    rpge0
    adantl
    @9
    cB
    @4
    @0
    @1
    @8
    simplr
    #
    @8
    @4
    cr
    wcel
    @2
    @4
    rpre
    adantl
    #
    addge01d
    mpbid
    @9
    @0
    cB
    cxr
    wcel
    #
    @5
    cxr
    wcel
    @3
    @10
    wa
    @6
    wi
    @0
    @1
    @8
    simpll
    @9
    cB
    @12
    rexrd
    @9
    @5
    @9
    cB
    @4
    @12
    @13
    readdcld
    rexrd
    cA
    cB
    @5
    xrletr
    syl3anc
    mpan2d
    ralrimdva
    @2
    @7
    cB
    cA
    clt
    wbr
    #
    wn
    #
    @3
    @2
    @15
    @7
    @2
    @15
    cB
    vy
    cv
    #
    clt
    wbr
    #
    @17
    cA
    clt
    wbr
    #
    wa
    #
    vy
    cq
    wrex
    #
    @7
    wn
    #
    @2
    @14
    @0
    @15
    @21
    wi
    @1
    @14
    @0
    cB
    rexr
    #
    adantl
    @0
    @1
    simpl
    @14
    @0
    @15
    @21
    vy
    cB
    cA
    qbtwnxr
    3expia
    syl2anc
    @2
    @20
    @22
    vy
    cq
    @2
    @17
    cq
    wcel
    #
    @20
    wa
    #
    wa
    #
    @6
    wn
    #
    vx
    crp
    wrex
    #
    @22
    @26
    @17
    cB
    cmin
    co
    #
    crp
    wcel
    #
    cA
    cB
    @29
    caddc
    co
    #
    cle
    wbr
    #
    wn
    #
    @28
    @26
    @18
    @30
    @2
    @24
    @18
    @19
    simprrl
    @26
    @1
    @17
    cr
    wcel
    #
    @18
    @30
    wb
    @0
    @1
    @25
    simplr
    #
    @24
    @34
    @2
    @20
    @17
    qre
    ad2antrl
    #
    cB
    @17
    difrp
    syl2anc
    mpbid
    @26
    @32
    cA
    @17
    cle
    wbr
    #
    @26
    @19
    @37
    wn
    #
    @2
    @24
    @18
    @19
    simprrr
    @26
    @17
    cxr
    wcel
    @0
    @19
    @38
    wb
    @26
    @17
    @36
    rexrd
    @0
    @1
    @25
    simpll
    @17
    cA
    xrltnle
    syl2anc
    mpbid
    @26
    @31
    @17
    cA
    cle
    @26
    cB
    @17
    @26
    cB
    @35
    recnd
    @26
    @17
    @36
    recnd
    pncan3d
    breq2d
    mtbird
    @27
    @33
    vx
    @29
    crp
    @4
    @29
    wceq
    #
    @6
    @32
    @39
    @5
    @31
    cA
    cle
    @4
    @29
    cB
    caddc
    oveq2
    breq2d
    notbid
    rspcev
    syl2anc
    @6
    vx
    crp
    rexnal
    sylib
    rexlimdvaa
    syld
    con2d
    @1
    @0
    @14
    @3
    @16
    wb
    @23
    cA
    cB
    xrlenlt
    sylan2
    sylibrd
    impbid
end
