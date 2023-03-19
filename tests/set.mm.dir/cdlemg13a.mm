include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "wne.mm"
include "wceq.mm"
include "co.mm"
include "simp11l.mm"
include "simp12l.mm"
include "simp11.mm"
include "simp2r.mm"
include "ltrnat.mm"
include "syl3anc.mm"
include "hlatlej1.mm"
include "simp32.mm"
include "simp2l.mm"
include "simp12.mm"
include "ltrnel.mm"
include "trlval2.mm"
include "3eqtr3d.mm"
include "oveq2d.mm"
include "ltrncoat.mm"
include "syl121anc.mm"
include "eqid.mm"
include "cdleme0cp.mm"
include "syl12anc.mm"
include "cdleme0cq.mm"
include "3eqtr3rd.mm"
include "breqtrd.mm"
include "hlatlej2.mm"
include "clat.mm"
include "cbs.mm"
include "wb.mm"
include "hllat.mm"
include "syl.mm"
include "atbase.mm"
include "hlatjcl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "simp13.mm"
include "simp33.mm"
include "cdlemg11a.mm"
include "syl123anc.mm"
include "necomd.mm"
include "ps-1.mm"
include "syl132anc.mm"
include "mpbid.mm"

theorem cdlemg13a
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdlemg12.l: |- .<_ = ( le ` K )
  assume cdlemg12.j: |- .\/ = ( join ` K )
  assume cdlemg12.m: |- ./\ = ( meet ` K )
  assume cdlemg12.a: |- A = ( Atoms ` K )
  assume cdlemg12.h: |- H = ( LHyp ` K )
  assume cdlemg12.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg12b.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T ) /\ ( ( F ` P ) =/= P /\ ( R ` F ) = ( R ` G ) /\ ( ( F ` ( G ` P ) ) .\/ ( F ` ( G ` Q ) ) ) =/= ( P .\/ Q ) ) ) -> ( P .\/ ( F ` ( G ` P ) ) ) = ( ( G ` P ) .\/ ( F ` ( G ` P ) ) ) )

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
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    cF
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    wa
    #
    cP
    cF
    cfv
    cP
    wne
    #
    cF
    cR
    cfv
    #
    cG
    cR
    cfv
    #
    wceq
    #
    cP
    cG
    cfv
    #
    cF
    cfv
    #
    cQ
    cG
    cfv
    cF
    cfv
    c.or
    co
    cP
    cQ
    c.or
    co
    wne
    #
    w3a
    #
    w3a
    #
    cP
    @16
    c.or
    co
    #
    @15
    @16
    c.or
    co
    #
    c.le
    wbr
    #
    @20
    @21
    wceq
    #
    @19
    cP
    @21
    c.le
    wbr
    #
    @16
    @21
    c.le
    wbr
    #
    @22
    @19
    cP
    cP
    @15
    c.or
    co
    #
    @21
    c.le
    @19
    @0
    @3
    @15
    cA
    wcel
    #
    cP
    @26
    c.le
    wbr
    @0
    @1
    @5
    @6
    @10
    @18
    simp11l
    #
    @3
    @4
    @2
    @6
    @10
    @18
    simp12l
    #
    @19
    @2
    @9
    @3
    @27
    @2
    @5
    @6
    @10
    @18
    simp11
    #
    @7
    @8
    @9
    @18
    simp2r
    #
    @29
    cA
    cP
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemg12.l
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    ltrnat
    syl3anc
    #
    cA
    cP
    @15
    c.or
    cK
    c.le
    cdlemg12.l
    cdlemg12.j
    cdlemg12.a
    hlatlej1
    syl3anc
    @19
    @15
    @21
    cW
    c.an
    co
    #
    c.or
    co
    #
    @15
    @26
    cW
    c.an
    co
    #
    c.or
    co
    #
    @21
    @26
    @19
    @33
    @35
    @15
    c.or
    @19
    @12
    @13
    @33
    @35
    @7
    @10
    @11
    @14
    @17
    simp32
    @19
    @2
    @8
    @27
    @15
    cW
    c.le
    wbr
    wn
    wa
    #
    @12
    @33
    wceq
    @30
    @7
    @8
    @9
    @18
    simp2l
    #
    @19
    @2
    @9
    @5
    @37
    @30
    @31
    @2
    @5
    @6
    @10
    @18
    simp12
    #
    cA
    cP
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemg12.l
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    ltrnel
    syl3anc
    #
    cA
    @15
    cR
    cT
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    trlval2
    syl3anc
    @19
    @2
    @9
    @5
    @13
    @35
    wceq
    @30
    @31
    @39
    cA
    cP
    cR
    cT
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    trlval2
    syl3anc
    3eqtr3d
    oveq2d
    @19
    @2
    @37
    @16
    cA
    wcel
    #
    @34
    @21
    wceq
    @30
    @40
    @19
    @2
    @8
    @9
    @3
    @41
    @30
    @38
    @31
    @29
    cA
    cP
    cT
    cF
    cG
    cH
    cK
    c.le
    cW
    cdlemg12.l
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    ltrncoat
    syl121anc
    #
    cA
    @15
    @16
    @33
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    @33
    eqid
    cdleme0cp
    syl12anc
    @19
    @2
    @3
    @37
    @36
    @26
    wceq
    @30
    @29
    @40
    cA
    cP
    @15
    @35
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    @35
    eqid
    cdleme0cq
    syl12anc
    3eqtr3rd
    breqtrd
    @19
    @0
    @27
    @41
    @25
    @28
    @32
    @42
    cA
    @15
    @16
    c.or
    cK
    c.le
    cdlemg12.l
    cdlemg12.j
    cdlemg12.a
    hlatlej2
    syl3anc
    @19
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
    @16
    @44
    wcel
    #
    @21
    @44
    wcel
    #
    @24
    @25
    wa
    @22
    wb
    @19
    @0
    @43
    @28
    cK
    hllat
    syl
    @19
    @3
    @45
    @29
    cA
    @44
    cP
    cK
    @44
    eqid
    #
    cdlemg12.a
    atbase
    syl
    @19
    @41
    @46
    @42
    cA
    @44
    @16
    cK
    @48
    cdlemg12.a
    atbase
    syl
    @19
    @0
    @27
    @41
    @47
    @28
    @32
    @42
    cA
    @44
    c.or
    cK
    @15
    @16
    @48
    cdlemg12.j
    cdlemg12.a
    hlatjcl
    syl3anc
    @44
    c.or
    cK
    c.le
    cP
    @16
    @21
    @48
    cdlemg12.l
    cdlemg12.j
    latjle12
    syl13anc
    mpbi2and
    @19
    @0
    @3
    @41
    cP
    @16
    wne
    @27
    @41
    @22
    @23
    wb
    @28
    @29
    @42
    @19
    @16
    cP
    @19
    @2
    @5
    @6
    @8
    @9
    @17
    @16
    cP
    wne
    @30
    @39
    @2
    @5
    @6
    @10
    @18
    simp13
    @38
    @31
    @7
    @10
    @11
    @14
    @17
    simp33
    cA
    cP
    cQ
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg11a
    syl123anc
    necomd
    @32
    @42
    cA
    cP
    @16
    @15
    @16
    c.or
    cK
    c.le
    cdlemg12.l
    cdlemg12.j
    cdlemg12.a
    ps-1
    syl132anc
    mpbid
end
