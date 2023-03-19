include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "wne.mm"
include "co.mm"
include "wrex.mm"
include "simp1l.mm"
include "simp3l.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp3r.mm"
include "nbrne2.mm"
include "necomd.mm"
include "syl2anc.mm"
include "hlsupr.mm"
include "syl31anc.mm"
include "simp31.mm"
include "simp13r.mm"
include "simp12r.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wb.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "atbase.mm"
include "3ad2ant2.mm"
include "simp12l.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "biimpd.mm"
include "mpan2d.mm"
include "simp33.mm"
include "clc.mm"
include "wi.mm"
include "hlcvl.mm"
include "simp2.mm"
include "simp13l.mm"
include "simp32.mm"
include "cvlatexch2.mm"
include "syl131anc.mm"
include "mpd.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "lattr.mm"
include "mpand.mm"
include "syld.mm"
include "mtod.mm"
include "cvlatexch1.mm"
include "3jca.mm"
include "3exp.mm"
include "reximdvai.mm"

theorem cdlemf1
  let cA: class A
  let cP: class P
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vq: setvar q
  let vp: setvar p
  assume cdlemf1.l: |- .<_ = ( le ` K )
  assume cdlemf1.j: |- .\/ = ( join ` K )
  assume cdlemf1.a: |- A = ( Atoms ` K )
  assume cdlemf1.h: |- H = ( LHyp ` K )

  disjoint A q
  disjoint H q
  disjoint K q
  disjoint .<_ q
  disjoint P q
  disjoint U q
  disjoint W q
  disjoint p q
  disjoint A p
  disjoint H p
  disjoint K p
  disjoint .<_ p
  disjoint U p
  disjoint W p
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( U e. A /\ U .<_ W ) /\ ( P e. A /\ -. P .<_ W ) ) -> E. q e. A ( P =/= q /\ -. q .<_ W /\ U .<_ ( P .\/ q ) ) )

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
    cU
    cA
    wcel
    #
    cU
    cW
    c.le
    wbr
    #
    wa
    #
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    w3a
    #
    vq
    cv
    #
    cP
    wne
    #
    @11
    cU
    wne
    #
    @11
    cP
    cU
    c.or
    co
    c.le
    wbr
    #
    w3a
    #
    vq
    cA
    wrex
    #
    cP
    @11
    wne
    #
    @11
    cW
    c.le
    wbr
    #
    wn
    #
    cU
    cP
    @11
    c.or
    co
    c.le
    wbr
    #
    w3a
    #
    vq
    cA
    wrex
    @10
    @0
    @6
    @3
    cP
    cU
    wne
    #
    @16
    @0
    @1
    @5
    @9
    simp1l
    @2
    @5
    @6
    @8
    simp3l
    @2
    @3
    @4
    @9
    simp2l
    @10
    @4
    @8
    @22
    @2
    @3
    @4
    @9
    simp2r
    @2
    @5
    @6
    @8
    simp3r
    @4
    @8
    wa
    cU
    cP
    cU
    cP
    cW
    c.le
    nbrne2
    necomd
    syl2anc
    cA
    cP
    cU
    c.or
    cK
    c.le
    vq
    cdlemf1.l
    cdlemf1.j
    cdlemf1.a
    hlsupr
    syl31anc
    @10
    @15
    @21
    vq
    cA
    @10
    @11
    cA
    wcel
    #
    @15
    @21
    @10
    @23
    @15
    w3a
    #
    @17
    @19
    @20
    @24
    @11
    cP
    @10
    @23
    @12
    @13
    @14
    simp31
    #
    necomd
    @24
    @18
    @7
    @6
    @8
    @2
    @5
    @23
    @15
    simp13r
    @24
    @18
    @11
    cU
    c.or
    co
    #
    cW
    c.le
    wbr
    #
    @7
    @24
    @18
    @4
    @27
    @3
    @4
    @2
    @9
    @23
    @15
    simp12r
    @24
    @18
    @4
    wa
    #
    @27
    @24
    cK
    clat
    wcel
    #
    @11
    cK
    cbs
    cfv
    #
    wcel
    #
    cU
    @30
    wcel
    #
    cW
    @30
    wcel
    #
    @28
    @27
    wb
    @24
    @0
    @29
    @0
    @1
    @5
    @9
    @23
    @15
    simp11l
    #
    cK
    hllat
    syl
    #
    @23
    @10
    @31
    @15
    cA
    @30
    @11
    cK
    @30
    eqid
    #
    cdlemf1.a
    atbase
    3ad2ant2
    @24
    @3
    @32
    @3
    @4
    @2
    @9
    @23
    @15
    simp12l
    #
    cA
    @30
    cU
    cK
    @36
    cdlemf1.a
    atbase
    syl
    @24
    @1
    @33
    @0
    @1
    @5
    @9
    @23
    @15
    simp11r
    @30
    cH
    cK
    cW
    @36
    cdlemf1.h
    lhpbase
    syl
    #
    @30
    c.or
    cK
    c.le
    @11
    cU
    cW
    @36
    cdlemf1.l
    cdlemf1.j
    latjle12
    syl13anc
    biimpd
    mpan2d
    @24
    cP
    @26
    c.le
    wbr
    #
    @27
    @7
    @24
    @14
    @39
    @10
    @23
    @12
    @13
    @14
    simp33
    #
    @24
    cK
    clc
    wcel
    #
    @23
    @6
    @3
    @13
    @14
    @39
    wi
    @24
    @0
    @41
    @34
    cK
    hlcvl
    syl
    #
    @10
    @23
    @15
    simp2
    #
    @6
    @8
    @2
    @5
    @23
    @15
    simp13l
    #
    @37
    @10
    @23
    @12
    @13
    @14
    simp32
    cA
    @11
    cP
    cU
    c.or
    cK
    c.le
    cdlemf1.l
    cdlemf1.j
    cdlemf1.a
    cvlatexch2
    syl131anc
    mpd
    @24
    @29
    cP
    @30
    wcel
    #
    @26
    @30
    wcel
    #
    @33
    @39
    @27
    wa
    @7
    wi
    @35
    @24
    @6
    @45
    @44
    cA
    @30
    cP
    cK
    @36
    cdlemf1.a
    atbase
    syl
    @24
    @0
    @23
    @3
    @46
    @34
    @43
    @37
    cA
    @30
    c.or
    cK
    @11
    cU
    @36
    cdlemf1.j
    cdlemf1.a
    hlatjcl
    syl3anc
    @38
    @30
    cK
    c.le
    cP
    @26
    cW
    @36
    cdlemf1.l
    lattr
    syl13anc
    mpand
    syld
    mtod
    @24
    @14
    @20
    @40
    @24
    @41
    @23
    @3
    @6
    @12
    @14
    @20
    wi
    @42
    @43
    @37
    @44
    @25
    cA
    @11
    cU
    cP
    c.or
    cK
    c.le
    cdlemf1.l
    cdlemf1.j
    cdlemf1.a
    cvlatexch1
    syl131anc
    mpd
    3jca
    3exp
    reximdvai
    mpd
end
