include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "simp1.mm"
include "simp3l.mm"
include "trlle.mm"
include "syl2anc.mm"
include "biantrud.mm"
include "clat.mm"
include "cbs.mm"
include "wb.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "trlcl.mm"
include "simp3r.mm"
include "simp2ll.mm"
include "ltrnat.mm"
include "syl3anc.mm"
include "simp2rl.mm"
include "hlatjcl.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "wceq.mm"
include "cdlemg10b.mm"
include "3adant3l.mm"
include "breq2d.mm"
include "3bitr4rd.mm"
include "3bitrd.mm"

theorem cdlemg10c
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
  assume cdlemg8.l: |- .<_ = ( le ` K )
  assume cdlemg8.j: |- .\/ = ( join ` K )
  assume cdlemg8.m: |- ./\ = ( meet ` K )
  assume cdlemg8.a: |- A = ( Atoms ` K )
  assume cdlemg8.h: |- H = ( LHyp ` K )
  assume cdlemg8.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg10.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T ) ) -> ( ( R ` F ) .<_ ( ( G ` P ) .\/ ( G ` Q ) ) <-> ( R ` F ) .<_ ( P .\/ Q ) ) )

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
    w3a
    #
    cF
    cR
    cfv
    #
    cP
    cG
    cfv
    #
    cQ
    cG
    cfv
    #
    c.or
    co
    #
    c.le
    wbr
    #
    @18
    @14
    cW
    c.le
    wbr
    #
    wa
    #
    @14
    @17
    cW
    c.an
    co
    #
    c.le
    wbr
    #
    @14
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    @13
    @19
    @18
    @13
    @2
    @10
    @19
    @2
    @9
    @12
    simp1
    #
    @2
    @9
    @10
    @11
    simp3l
    #
    cR
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg8.l
    cdlemg8.h
    cdlemg8.t
    cdlemg10.r
    trlle
    syl2anc
    #
    biantrud
    @13
    cK
    clat
    wcel
    #
    @14
    cK
    cbs
    cfv
    #
    wcel
    #
    @17
    @29
    wcel
    #
    cW
    @29
    wcel
    #
    @20
    @22
    wb
    @13
    @0
    @28
    @0
    @1
    @9
    @12
    simp1l
    #
    cK
    hllat
    syl
    #
    @13
    @2
    @10
    @30
    @25
    @26
    @29
    cR
    cT
    cF
    cH
    cK
    cW
    @29
    eqid
    #
    cdlemg8.h
    cdlemg8.t
    cdlemg10.r
    trlcl
    syl2anc
    #
    @13
    @0
    @15
    cA
    wcel
    #
    @16
    cA
    wcel
    #
    @31
    @33
    @13
    @2
    @11
    @3
    @37
    @25
    @2
    @9
    @10
    @11
    simp3r
    #
    @3
    @4
    @8
    @2
    @12
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
    cdlemg8.l
    cdlemg8.a
    cdlemg8.h
    cdlemg8.t
    ltrnat
    syl3anc
    @13
    @2
    @11
    @6
    @38
    @25
    @39
    @6
    @7
    @5
    @2
    @12
    simp2rl
    #
    cA
    cQ
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemg8.l
    cdlemg8.a
    cdlemg8.h
    cdlemg8.t
    ltrnat
    syl3anc
    cA
    @29
    c.or
    cK
    @15
    @16
    @35
    cdlemg8.j
    cdlemg8.a
    hlatjcl
    syl3anc
    @13
    @1
    @32
    @0
    @1
    @9
    @12
    simp1r
    @29
    cH
    cK
    cW
    @35
    cdlemg8.h
    lhpbase
    syl
    #
    @29
    cK
    c.le
    c.an
    @14
    @17
    cW
    @35
    cdlemg8.l
    cdlemg8.m
    latlem12
    syl13anc
    @13
    @24
    @19
    wa
    #
    @14
    @23
    cW
    c.an
    co
    #
    c.le
    wbr
    #
    @24
    @22
    @13
    @28
    @30
    @23
    @29
    wcel
    #
    @32
    @43
    @45
    wb
    @34
    @36
    @13
    @0
    @3
    @6
    @46
    @33
    @40
    @41
    cA
    @29
    c.or
    cK
    cP
    cQ
    @35
    cdlemg8.j
    cdlemg8.a
    hlatjcl
    syl3anc
    @42
    @29
    cK
    c.le
    c.an
    @14
    @23
    cW
    @35
    cdlemg8.l
    cdlemg8.m
    latlem12
    syl13anc
    @13
    @19
    @24
    @27
    biantrud
    @13
    @21
    @44
    @14
    c.le
    @2
    @9
    @11
    @21
    @44
    wceq
    @10
    cA
    cP
    cQ
    cT
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg8.l
    cdlemg8.j
    cdlemg8.m
    cdlemg8.a
    cdlemg8.h
    cdlemg8.t
    cdlemg10b
    3adant3l
    breq2d
    3bitr4rd
    3bitrd
end
