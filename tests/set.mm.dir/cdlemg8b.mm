include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wne.mm"
include "clat.mm"
include "cbs.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp21l.mm"
include "eqid.mm"
include "atbase.mm"
include "simp22l.mm"
include "latlej1.mm"
include "syl3anc.mm"
include "simp1.mm"
include "simp23.mm"
include "simp31.mm"
include "simp21.mm"
include "ltrnel.mm"
include "simpld.mm"
include "ltrncl.mm"
include "simp32.mm"
include "breqtrd.mm"
include "wb.mm"
include "hlatjcl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "simp33.mm"
include "necomd.mm"
include "ps-1.mm"
include "syl132anc.mm"
include "mpbid.mm"

theorem cdlemg8b
  let cA: class A
  let cP: class P
  let cQ: class Q
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ F e. T ) /\ ( G e. T /\ ( ( F ` ( G ` P ) ) .\/ ( F ` ( G ` Q ) ) ) = ( P .\/ Q ) /\ ( F ` ( G ` P ) ) =/= P ) ) -> ( P .\/ ( F ` ( G ` P ) ) ) = ( P .\/ Q ) )

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
    cF
    cT
    wcel
    #
    w3a
    #
    cG
    cT
    wcel
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
    #
    cF
    cfv
    #
    c.or
    co
    #
    cP
    cQ
    c.or
    co
    #
    wceq
    #
    @13
    cP
    wne
    #
    w3a
    #
    w3a
    #
    cP
    @13
    c.or
    co
    #
    @17
    c.le
    wbr
    #
    @22
    @17
    wceq
    #
    @21
    cP
    @17
    c.le
    wbr
    #
    @13
    @17
    c.le
    wbr
    #
    @23
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
    cQ
    @28
    wcel
    #
    @25
    @21
    @0
    @27
    @0
    @1
    @10
    @20
    simp1l
    #
    cK
    hllat
    syl
    #
    @21
    @3
    @29
    @3
    @4
    @8
    @9
    @2
    @20
    simp21l
    #
    cA
    @28
    cP
    cK
    @28
    eqid
    #
    cdlemg8.a
    atbase
    syl
    #
    @21
    @6
    @30
    @6
    @7
    @5
    @9
    @2
    @20
    simp22l
    #
    cA
    @28
    cQ
    cK
    @34
    cdlemg8.a
    atbase
    syl
    #
    @28
    c.or
    cK
    c.le
    cP
    cQ
    @34
    cdlemg8.l
    cdlemg8.j
    latlej1
    syl3anc
    @21
    @13
    @16
    @17
    c.le
    @21
    @27
    @13
    @28
    wcel
    #
    @15
    @28
    wcel
    #
    @13
    @16
    c.le
    wbr
    @32
    @21
    @13
    cA
    wcel
    #
    @38
    @21
    @2
    @9
    @12
    cA
    wcel
    @12
    cW
    c.le
    wbr
    wn
    wa
    #
    @40
    @2
    @10
    @20
    simp1
    #
    @2
    @5
    @8
    @9
    @20
    simp23
    #
    @21
    @2
    @11
    @5
    @41
    @42
    @2
    @10
    @11
    @18
    @19
    simp31
    #
    @2
    @5
    @8
    @9
    @20
    simp21
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
    ltrnel
    syl3anc
    @2
    @9
    @41
    w3a
    @40
    @13
    cW
    c.le
    wbr
    wn
    cA
    @12
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg8.l
    cdlemg8.a
    cdlemg8.h
    cdlemg8.t
    ltrnel
    simpld
    syl3anc
    #
    cA
    @28
    @13
    cK
    @34
    cdlemg8.a
    atbase
    syl
    #
    @21
    @2
    @9
    @14
    @28
    wcel
    #
    @39
    @42
    @43
    @21
    @2
    @11
    @30
    @47
    @42
    @44
    @37
    @28
    cT
    cG
    cH
    cK
    chlt
    cW
    cQ
    @34
    cdlemg8.h
    cdlemg8.t
    ltrncl
    syl3anc
    @28
    cT
    cF
    cH
    cK
    chlt
    cW
    @14
    @34
    cdlemg8.h
    cdlemg8.t
    ltrncl
    syl3anc
    @28
    c.or
    cK
    c.le
    @13
    @15
    @34
    cdlemg8.l
    cdlemg8.j
    latlej1
    syl3anc
    @2
    @10
    @11
    @18
    @19
    simp32
    breqtrd
    @21
    @27
    @29
    @38
    @17
    @28
    wcel
    #
    @25
    @26
    wa
    @23
    wb
    @32
    @35
    @46
    @21
    @0
    @3
    @6
    @48
    @31
    @33
    @36
    cA
    @28
    c.or
    cK
    cP
    cQ
    @34
    cdlemg8.j
    cdlemg8.a
    hlatjcl
    syl3anc
    @28
    c.or
    cK
    c.le
    cP
    @13
    @17
    @34
    cdlemg8.l
    cdlemg8.j
    latjle12
    syl13anc
    mpbi2and
    @21
    @0
    @3
    @40
    cP
    @13
    wne
    @3
    @6
    @23
    @24
    wb
    @31
    @33
    @45
    @21
    @13
    cP
    @2
    @10
    @11
    @18
    @19
    simp33
    necomd
    @33
    @36
    cA
    cP
    @13
    cP
    cQ
    c.or
    cK
    c.le
    cdlemg8.l
    cdlemg8.j
    cdlemg8.a
    ps-1
    syl132anc
    mpbid
end
