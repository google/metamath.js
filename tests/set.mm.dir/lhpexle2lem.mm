include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "wne.mm"
include "wrex.mm"
include "wceq.mm"
include "simpl1.mm"
include "lhpexle1.mm"
include "syl.mm"
include "simp3l.mm"
include "simp3r.mm"
include "simp2.mm"
include "neeqtrd.mm"
include "3jca.mm"
include "3expia.mm"
include "reximdv.mm"
include "mpd.mm"
include "cjn.mm"
include "cfv.mm"
include "co.mm"
include "simpl1l.mm"
include "simpl2l.mm"
include "simpl3l.mm"
include "simpr.mm"
include "eqid.mm"
include "hlsupr.mm"
include "syl31anc.mm"
include "wi.mm"
include "cbs.mm"
include "clat.mm"
include "hllat.mm"
include "simprlr.mm"
include "atbase.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simpl1r.mm"
include "lhpbase.mm"
include "simprr3.mm"
include "simpl2r.mm"
include "simpl3r.mm"
include "wb.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "lattrd.mm"
include "simprr1.mm"
include "simprr2.mm"
include "exp44.mm"
include "imp31.mm"
include "reximdva.mm"
include "pm2.61dane.mm"

theorem lhpexle2lem
  let cA: class A
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let cY: class Y
  let vp: setvar p
  let cZ: class Z
  assume lhpex1.l: |- .<_ = ( le ` K )
  assume lhpex1.a: |- A = ( Atoms ` K )
  assume lhpex1.h: |- H = ( LHyp ` K )

  disjoint .<_ p
  disjoint A p
  disjoint H p
  disjoint K p
  disjoint W p
  disjoint X p
  disjoint Y p
  disjoint Z p
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. A /\ X .<_ W ) /\ ( Y e. A /\ Y .<_ W ) ) -> E. p e. A ( p .<_ W /\ p =/= X /\ p =/= Y ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cX
    cA
    wcel
    #
    cX
    cW
    c.le
    wbr
    #
    wa
    #
    cY
    cA
    wcel
    #
    cY
    cW
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    vp
    cv
    #
    cW
    c.le
    wbr
    #
    @10
    cX
    wne
    #
    @10
    cY
    wne
    #
    w3a
    #
    vp
    cA
    wrex
    #
    cX
    cY
    @9
    cX
    cY
    wceq
    #
    wa
    #
    @11
    @12
    wa
    #
    vp
    cA
    wrex
    #
    @15
    @17
    @2
    @19
    @2
    @5
    @8
    @16
    simpl1
    cA
    cH
    cK
    c.le
    cW
    cX
    vp
    lhpex1.l
    lhpex1.a
    lhpex1.h
    lhpexle1
    syl
    @17
    @18
    @14
    vp
    cA
    @9
    @16
    @18
    @14
    @9
    @16
    @18
    w3a
    #
    @11
    @12
    @13
    @9
    @16
    @11
    @12
    simp3l
    @9
    @16
    @11
    @12
    simp3r
    #
    @20
    @10
    cX
    cY
    @21
    @9
    @16
    @18
    simp2
    neeqtrd
    3jca
    3expia
    reximdv
    mpd
    @9
    cX
    cY
    wne
    #
    wa
    #
    @12
    @13
    @10
    cX
    cY
    cK
    cjn
    cfv
    #
    co
    #
    c.le
    wbr
    #
    w3a
    #
    vp
    cA
    wrex
    #
    @15
    @23
    @0
    @3
    @6
    @22
    @28
    @0
    @1
    @5
    @8
    @22
    simpl1l
    @3
    @4
    @2
    @8
    @22
    simpl2l
    @6
    @7
    @2
    @5
    @22
    simpl3l
    @9
    @22
    simpr
    cA
    cX
    cY
    @24
    cK
    c.le
    vp
    lhpex1.l
    @24
    eqid
    #
    lhpex1.a
    hlsupr
    syl31anc
    @23
    @27
    @14
    vp
    cA
    @9
    @22
    @10
    cA
    wcel
    #
    @27
    @14
    wi
    @9
    @22
    @30
    @27
    @14
    @9
    @22
    @30
    wa
    #
    @27
    wa
    #
    wa
    #
    @11
    @12
    @13
    @33
    cK
    cbs
    cfv
    #
    cK
    c.le
    @10
    @25
    cW
    @34
    eqid
    #
    lhpex1.l
    @33
    @0
    cK
    clat
    wcel
    #
    @0
    @1
    @5
    @8
    @32
    simpl1l
    #
    cK
    hllat
    syl
    #
    @33
    @30
    @10
    @34
    wcel
    @9
    @22
    @30
    @27
    simprlr
    cA
    @34
    @10
    cK
    @35
    lhpex1.a
    atbase
    syl
    @33
    @0
    @3
    @6
    @25
    @34
    wcel
    @37
    @3
    @4
    @2
    @8
    @32
    simpl2l
    #
    @6
    @7
    @2
    @5
    @32
    simpl3l
    #
    cA
    @34
    @24
    cK
    cX
    cY
    @35
    @29
    lhpex1.a
    hlatjcl
    syl3anc
    @33
    @1
    cW
    @34
    wcel
    #
    @0
    @1
    @5
    @8
    @32
    simpl1r
    @34
    cH
    cK
    cW
    @35
    lhpex1.h
    lhpbase
    syl
    #
    @12
    @13
    @26
    @31
    @9
    simprr3
    @33
    @4
    @7
    @25
    cW
    c.le
    wbr
    #
    @3
    @4
    @2
    @8
    @32
    simpl2r
    @6
    @7
    @2
    @5
    @32
    simpl3r
    @33
    @36
    cX
    @34
    wcel
    #
    cY
    @34
    wcel
    #
    @41
    @4
    @7
    wa
    @43
    wb
    @38
    @33
    @3
    @44
    @39
    cA
    @34
    cX
    cK
    @35
    lhpex1.a
    atbase
    syl
    @33
    @6
    @45
    @40
    cA
    @34
    cY
    cK
    @35
    lhpex1.a
    atbase
    syl
    @42
    @34
    @24
    cK
    c.le
    cX
    cY
    cW
    @35
    lhpex1.l
    @29
    latjle12
    syl13anc
    mpbi2and
    lattrd
    @12
    @13
    @26
    @31
    @9
    simprr1
    @12
    @13
    @26
    @31
    @9
    simprr2
    3jca
    exp44
    imp31
    reximdva
    mpd
    pm2.61dane
end
