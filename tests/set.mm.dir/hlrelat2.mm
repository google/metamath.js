include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "cmee.mm"
include "cfv.mm"
include "co.mm"
include "cplt.mm"
include "clat.mm"
include "wb.mm"
include "hllat.mm"
include "eqid.mm"
include "latnlemlt.mm"
include "syl3an1.mm"
include "cjn.mm"
include "wi.mm"
include "simp1.mm"
include "latmcl.mm"
include "simp2.mm"
include "hlrelat.mm"
include "ex.mm"
include "syl3anc.mm"
include "simpl1.mm"
include "syl.mm"
include "adantr.mm"
include "atbase.mm"
include "adantl.mm"
include "simpl2.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "simpr.mm"
include "syl6bir.mm"
include "adantld.mm"
include "simpl3.mm"
include "latlem12.mm"
include "notbid.mm"
include "latnle.mm"
include "bitrd.mm"
include "anbi12d.mm"
include "pm3.21.mm"
include "wo.mm"
include "orcom.mm"
include "pm4.55.mm"
include "imor.mm"
include "3bitr4ri.mm"
include "sylib.mm"
include "con2i.mm"
include "adantrl.mm"
include "jcad.mm"
include "reximdva.mm"
include "syld.mm"
include "sylbid.mm"
include "wral.mm"
include "lattr.mm"
include "exp4b.mm"
include "com34.mm"
include "com23.mm"
include "ralrimdv.mm"
include "iman.mm"
include "ralbii.mm"
include "ralnex.mm"
include "bitri.mm"
include "syl6ib.mm"
include "con2d.mm"
include "impbid.mm"

theorem hlrelat2
  let cA: class A
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume hlrelat2.b: |- B = ( Base ` K )
  assume hlrelat2.l: |- .<_ = ( le ` K )
  assume hlrelat2.a: |- A = ( Atoms ` K )

  disjoint A p
  disjoint B p
  disjoint K p
  disjoint .<_ p
  disjoint X p
  disjoint Y p
  assert |- ( ( K e. HL /\ X e. B /\ Y e. B ) -> ( -. X .<_ Y <-> E. p e. A ( p .<_ X /\ -. p .<_ Y ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    c.le
    wbr
    #
    wn
    #
    vp
    cv
    #
    cX
    c.le
    wbr
    #
    @6
    cY
    c.le
    wbr
    #
    wn
    #
    wa
    #
    vp
    cA
    wrex
    #
    @3
    @5
    cX
    cY
    cK
    cmee
    cfv
    #
    co
    #
    cX
    cK
    cplt
    cfv
    #
    wbr
    #
    @11
    @0
    cK
    clat
    wcel
    #
    @1
    @2
    @5
    @15
    wb
    cK
    hllat
    #
    cB
    @14
    cK
    c.le
    @12
    cX
    cY
    hlrelat2.b
    hlrelat2.l
    @14
    eqid
    #
    @12
    eqid
    #
    latnlemlt
    syl3an1
    @3
    @15
    @13
    @13
    @6
    cK
    cjn
    cfv
    #
    co
    #
    @14
    wbr
    #
    @21
    cX
    c.le
    wbr
    #
    wa
    #
    vp
    cA
    wrex
    #
    @11
    @3
    @0
    @13
    cB
    wcel
    #
    @1
    @15
    @25
    wi
    @0
    @1
    @2
    simp1
    @0
    @16
    @1
    @2
    @26
    @17
    cB
    cK
    @12
    cX
    cY
    hlrelat2.b
    @19
    latmcl
    syl3an1
    #
    @0
    @1
    @2
    simp2
    @0
    @26
    @1
    w3a
    @15
    @25
    cA
    cB
    @14
    @20
    cK
    c.le
    @13
    cX
    vp
    hlrelat2.b
    hlrelat2.l
    @18
    @20
    eqid
    #
    hlrelat2.a
    hlrelat
    ex
    syl3anc
    @3
    @24
    @10
    vp
    cA
    @3
    @6
    cA
    wcel
    #
    wa
    #
    @24
    @7
    @9
    @30
    @23
    @7
    @22
    @30
    @23
    @13
    cX
    c.le
    wbr
    #
    @7
    wa
    #
    @7
    @30
    @16
    @26
    @6
    cB
    wcel
    #
    @1
    @32
    @23
    wb
    @30
    @0
    @16
    @0
    @1
    @2
    @29
    simpl1
    @17
    syl
    #
    @3
    @26
    @29
    @27
    adantr
    #
    @29
    @33
    @3
    cA
    cB
    @6
    cK
    hlrelat2.b
    hlrelat2.a
    atbase
    adantl
    #
    @0
    @1
    @2
    @29
    simpl2
    #
    cB
    @20
    cK
    c.le
    @13
    @6
    cX
    hlrelat2.b
    hlrelat2.l
    @28
    latjle12
    syl13anc
    #
    @31
    @7
    simpr
    syl6bir
    adantld
    @30
    @24
    @7
    @8
    wa
    #
    wn
    #
    @32
    wa
    @9
    @30
    @40
    @22
    @32
    @23
    @30
    @40
    @6
    @13
    c.le
    wbr
    #
    wn
    #
    @22
    @30
    @39
    @41
    @30
    @16
    @33
    @1
    @2
    @39
    @41
    wb
    @34
    @36
    @37
    @0
    @1
    @2
    @29
    simpl3
    #
    cB
    cK
    c.le
    @12
    @6
    cX
    cY
    hlrelat2.b
    hlrelat2.l
    @19
    latlem12
    syl13anc
    notbid
    @30
    @16
    @26
    @33
    @42
    @22
    wb
    @34
    @35
    @36
    cB
    @14
    @20
    cK
    c.le
    @13
    @6
    hlrelat2.b
    hlrelat2.l
    @18
    @28
    latnle
    syl3anc
    bitrd
    @38
    anbi12d
    @40
    @7
    @9
    @31
    @8
    @40
    @7
    wa
    #
    @8
    @7
    @39
    wi
    #
    @44
    wn
    #
    @8
    @7
    pm3.21
    @39
    @7
    wn
    #
    wo
    @47
    @39
    wo
    @46
    @45
    @39
    @47
    orcom
    @39
    @7
    pm4.55
    @7
    @39
    imor
    3bitr4ri
    sylib
    con2i
    adantrl
    syl6bir
    jcad
    reximdva
    syld
    sylbid
    @3
    @4
    @11
    @3
    @4
    @7
    @8
    wi
    #
    vp
    cA
    wral
    #
    @11
    wn
    #
    @3
    @4
    @48
    vp
    cA
    @3
    @29
    @4
    @48
    @3
    @29
    @7
    @4
    @8
    @3
    @29
    @7
    @4
    @8
    @30
    @16
    @33
    @1
    @2
    @7
    @4
    wa
    @8
    wi
    @34
    @36
    @37
    @43
    cB
    cK
    c.le
    @6
    cX
    cY
    hlrelat2.b
    hlrelat2.l
    lattr
    syl13anc
    exp4b
    com34
    com23
    ralrimdv
    @49
    @10
    wn
    #
    vp
    cA
    wral
    @50
    @48
    @51
    vp
    cA
    @7
    @8
    iman
    ralbii
    @10
    vp
    cA
    ralnex
    bitri
    syl6ib
    con2d
    impbid
end
