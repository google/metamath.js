include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "w3a.mm"
include "cfv.mm"
include "wne.mm"
include "co.mm"
include "simp11.mm"
include "simp12.mm"
include "simp31.mm"
include "simp13.mm"
include "simp2r.mm"
include "simp33.mm"
include "trlat.mm"
include "syl112anc.mm"
include "trlle.mm"
include "syl2anc.mm"
include "lhp2atnle.mm"
include "syl312anc.mm"
include "simp11l.mm"
include "simp12l.mm"
include "simp13l.mm"
include "hlatlej1.mm"
include "syl3anc.mm"
include "simp32.mm"
include "clat.mm"
include "cbs.mm"
include "wb.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "atbase.mm"
include "simp2l.mm"
include "hlatjcl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "wi.mm"
include "lattr.mm"
include "mpan2d.mm"
include "mtod.mm"

theorem cdlemg27a
  let vz: setvar z
  let vv: setvar v
  let cA: class A
  let cP: class P
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vr: setvar r
  let cG: class G
  let cQ: class Q
  let cS: class S
  assume cdlemg12.l: |- .<_ = ( le ` K )
  assume cdlemg12.j: |- .\/ = ( join ` K )
  assume cdlemg12.m: |- ./\ = ( meet ` K )
  assume cdlemg12.a: |- A = ( Atoms ` K )
  assume cdlemg12.h: |- H = ( LHyp ` K )
  assume cdlemg12.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg12b.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( v e. A /\ v .<_ W ) ) /\ ( z e. A /\ F e. T ) /\ ( v =/= ( R ` F ) /\ z .<_ ( P .\/ v ) /\ ( F ` P ) =/= P ) ) -> -. ( R ` F ) .<_ ( P .\/ z ) )

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
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    vv
    cv
    #
    cA
    wcel
    #
    @6
    cW
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    vz
    cv
    #
    cA
    wcel
    #
    cF
    cT
    wcel
    #
    wa
    #
    @6
    cF
    cR
    cfv
    #
    wne
    #
    @11
    cP
    @6
    c.or
    co
    #
    c.le
    wbr
    #
    cP
    cF
    cfv
    cP
    wne
    #
    w3a
    #
    w3a
    #
    @15
    cP
    @11
    c.or
    co
    #
    c.le
    wbr
    #
    @15
    @17
    c.le
    wbr
    #
    @21
    @2
    @5
    @16
    @9
    @15
    cA
    wcel
    #
    @15
    cW
    c.le
    wbr
    #
    @24
    wn
    @2
    @5
    @9
    @14
    @20
    simp11
    #
    @2
    @5
    @9
    @14
    @20
    simp12
    #
    @10
    @14
    @16
    @18
    @19
    simp31
    @2
    @5
    @9
    @14
    @20
    simp13
    @21
    @2
    @5
    @13
    @19
    @25
    @27
    @28
    @10
    @12
    @13
    @20
    simp2r
    #
    @10
    @14
    @16
    @18
    @19
    simp33
    cA
    cP
    cR
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg12.l
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    trlat
    syl112anc
    #
    @21
    @2
    @13
    @26
    @27
    @29
    cR
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg12.l
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    trlle
    syl2anc
    cA
    cP
    @6
    cH
    c.or
    cK
    c.le
    @15
    cW
    cdlemg12.l
    cdlemg12.j
    cdlemg12.a
    cdlemg12.h
    lhp2atnle
    syl312anc
    @21
    @23
    @22
    @17
    c.le
    wbr
    #
    @24
    @21
    cP
    @17
    c.le
    wbr
    #
    @18
    @31
    @21
    @0
    @3
    @7
    @32
    @0
    @1
    @5
    @9
    @14
    @20
    simp11l
    #
    @3
    @4
    @2
    @9
    @14
    @20
    simp12l
    #
    @7
    @8
    @2
    @5
    @14
    @20
    simp13l
    #
    cA
    cP
    @6
    c.or
    cK
    c.le
    cdlemg12.l
    cdlemg12.j
    cdlemg12.a
    hlatlej1
    syl3anc
    @10
    @14
    @16
    @18
    @19
    simp32
    @21
    cK
    clat
    wcel
    #
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    @11
    @37
    wcel
    #
    @17
    @37
    wcel
    #
    @32
    @18
    wa
    @31
    wb
    @21
    @0
    @36
    @33
    cK
    hllat
    syl
    #
    @21
    @3
    @38
    @34
    cA
    @37
    cP
    cK
    @37
    eqid
    #
    cdlemg12.a
    atbase
    syl
    @21
    @12
    @39
    @10
    @12
    @13
    @20
    simp2l
    #
    cA
    @37
    @11
    cK
    @42
    cdlemg12.a
    atbase
    syl
    @21
    @0
    @3
    @7
    @40
    @33
    @34
    @35
    cA
    @37
    c.or
    cK
    cP
    @6
    @42
    cdlemg12.j
    cdlemg12.a
    hlatjcl
    syl3anc
    #
    @37
    c.or
    cK
    c.le
    cP
    @11
    @17
    @42
    cdlemg12.l
    cdlemg12.j
    latjle12
    syl13anc
    mpbi2and
    @21
    @36
    @15
    @37
    wcel
    #
    @22
    @37
    wcel
    #
    @40
    @23
    @31
    wa
    @24
    wi
    @41
    @21
    @25
    @45
    @30
    cA
    @37
    @15
    cK
    @42
    cdlemg12.a
    atbase
    syl
    @21
    @0
    @3
    @12
    @46
    @33
    @34
    @43
    cA
    @37
    c.or
    cK
    cP
    @11
    @42
    cdlemg12.j
    cdlemg12.a
    hlatjcl
    syl3anc
    @44
    @37
    cK
    c.le
    @15
    @22
    @17
    @42
    cdlemg12.l
    lattr
    syl13anc
    mpan2d
    mtod
end
