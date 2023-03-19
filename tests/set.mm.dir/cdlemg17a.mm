include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "co.mm"
include "w3a.mm"
include "cbs.mm"
include "eqid.mm"
include "clat.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp1.mm"
include "simp3l.mm"
include "simp2ll.mm"
include "ltrnat.mm"
include "syl3anc.mm"
include "atbase.mm"
include "hlatjcl.mm"
include "simp2rl.mm"
include "hlatlej2.mm"
include "wceq.mm"
include "simp2l.mm"
include "cdleme0cp.mm"
include "syl12anc.mm"
include "hlatlej1.mm"
include "trlval2.mm"
include "simp3r.mm"
include "eqbrtrrd.mm"
include "wb.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "lattrd.mm"

theorem cdlemg17a
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( G e. T /\ ( R ` G ) .<_ ( P .\/ Q ) ) ) -> ( G ` P ) .<_ ( P .\/ Q ) )

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
    #
    cQ
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    wa
    #
    cG
    cT
    wcel
    #
    cG
    cR
    cfv
    #
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    cK
    cbs
    cfv
    #
    cK
    c.le
    cP
    cG
    cfv
    #
    cP
    @17
    c.or
    co
    #
    @12
    @16
    eqid
    #
    cdlemg12.l
    @15
    @0
    cK
    clat
    wcel
    #
    @0
    @1
    @9
    @14
    simp1l
    #
    cK
    hllat
    syl
    #
    @15
    @17
    cA
    wcel
    #
    @17
    @16
    wcel
    @15
    @2
    @10
    @3
    @23
    @2
    @9
    @14
    simp1
    #
    @2
    @9
    @10
    @13
    simp3l
    #
    @3
    @4
    @8
    @2
    @14
    simp2ll
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
    ltrnat
    syl3anc
    #
    cA
    @16
    @17
    cK
    @19
    cdlemg12.a
    atbase
    syl
    @15
    @0
    @3
    @23
    @18
    @16
    wcel
    #
    @21
    @26
    @27
    cA
    @16
    c.or
    cK
    cP
    @17
    @19
    cdlemg12.j
    cdlemg12.a
    hlatjcl
    syl3anc
    #
    @15
    @0
    @3
    @6
    @12
    @16
    wcel
    #
    @21
    @26
    @6
    @7
    @5
    @2
    @14
    simp2rl
    #
    cA
    @16
    c.or
    cK
    cP
    cQ
    @19
    cdlemg12.j
    cdlemg12.a
    hlatjcl
    syl3anc
    #
    @15
    @0
    @3
    @23
    @17
    @18
    c.le
    wbr
    @21
    @26
    @27
    cA
    cP
    @17
    c.or
    cK
    c.le
    cdlemg12.l
    cdlemg12.j
    cdlemg12.a
    hlatlej2
    syl3anc
    @15
    cP
    @18
    cW
    c.an
    co
    #
    c.or
    co
    #
    @18
    @12
    c.le
    @15
    @2
    @5
    @23
    @34
    @18
    wceq
    @24
    @2
    @5
    @8
    @14
    simp2l
    #
    @27
    cA
    cP
    @17
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
    @15
    cP
    @12
    c.le
    wbr
    #
    @33
    @12
    c.le
    wbr
    #
    @34
    @12
    c.le
    wbr
    #
    @15
    @0
    @3
    @6
    @36
    @21
    @26
    @31
    cA
    cP
    cQ
    c.or
    cK
    c.le
    cdlemg12.l
    cdlemg12.j
    cdlemg12.a
    hlatlej1
    syl3anc
    @15
    @11
    @33
    @12
    c.le
    @15
    @2
    @10
    @5
    @11
    @33
    wceq
    @24
    @25
    @35
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
    @2
    @9
    @10
    @13
    simp3r
    eqbrtrrd
    @15
    @20
    cP
    @16
    wcel
    #
    @33
    @16
    wcel
    #
    @30
    @36
    @37
    wa
    @38
    wb
    @22
    @15
    @3
    @39
    @26
    cA
    @16
    cP
    cK
    @19
    cdlemg12.a
    atbase
    syl
    @15
    @20
    @28
    cW
    @16
    wcel
    #
    @40
    @22
    @29
    @15
    @1
    @41
    @0
    @1
    @9
    @14
    simp1r
    @16
    cH
    cK
    cW
    @19
    cdlemg12.h
    lhpbase
    syl
    @16
    cK
    c.an
    @18
    cW
    @19
    cdlemg12.m
    latmcl
    syl3anc
    @32
    @16
    c.or
    cK
    c.le
    cP
    @33
    @12
    @19
    cdlemg12.l
    cdlemg12.j
    latjle12
    syl13anc
    mpbi2and
    eqbrtrrd
    lattrd
end
