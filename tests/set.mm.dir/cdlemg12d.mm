include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp31.mm"
include "simp33.mm"
include "cdlemg12c.mm"
include "syl133anc.mm"
include "wceq.mm"
include "trlval4.mm"
include "syl132anc.mm"
include "ltrnel.mm"
include "syl3anc.mm"
include "simp12l.mm"
include "simp13l.mm"
include "ltrn11at.mm"
include "syl113anc.mm"
include "simp32.mm"
include "wb.mm"
include "simp2.mm"
include "cdlemg10c.mm"
include "syl121anc.mm"
include "mtbird.mm"
include "oveq1d.mm"
include "3brtr4d.mm"

theorem cdlemg12d
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T ) /\ ( P =/= Q /\ -. ( R ` F ) .<_ ( P .\/ Q ) /\ -. ( R ` G ) .<_ ( P .\/ Q ) ) ) -> ( R ` G ) .<_ ( ( R ` F ) .\/ ( ( ( F ` ( G ` P ) ) .\/ P ) ./\ ( ( F ` ( G ` Q ) ) .\/ Q ) ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
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
    cQ
    wne
    #
    cF
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
    wn
    #
    cG
    cR
    cfv
    #
    @13
    c.le
    wbr
    wn
    #
    w3a
    #
    w3a
    #
    cP
    cP
    cG
    cfv
    #
    c.or
    co
    cQ
    cQ
    cG
    cfv
    #
    c.or
    co
    c.an
    co
    #
    @20
    @20
    cF
    cfv
    #
    c.or
    co
    @21
    @21
    cF
    cfv
    #
    c.or
    co
    c.an
    co
    #
    @23
    cP
    c.or
    co
    @24
    cQ
    c.or
    co
    c.an
    co
    #
    c.or
    co
    #
    @16
    @12
    @26
    c.or
    co
    c.le
    @19
    @0
    @3
    @6
    @8
    @9
    @11
    @17
    @22
    @27
    c.le
    wbr
    @0
    @3
    @6
    @10
    @18
    simp11
    #
    @0
    @3
    @6
    @10
    @18
    simp12
    #
    @0
    @3
    @6
    @10
    @18
    simp13
    #
    @7
    @8
    @9
    @18
    simp2l
    #
    @7
    @8
    @9
    @18
    simp2r
    #
    @7
    @10
    @11
    @15
    @17
    simp31
    #
    @7
    @10
    @11
    @15
    @17
    simp33
    #
    cA
    cP
    cQ
    cR
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
    cdlemg12b.r
    cdlemg12c
    syl133anc
    @19
    @0
    @9
    @3
    @6
    @11
    @17
    @16
    @22
    wceq
    @28
    @32
    @29
    @30
    @33
    @34
    cA
    cP
    cQ
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
    trlval4
    syl132anc
    @19
    @12
    @25
    @26
    c.or
    @19
    @0
    @8
    @20
    cA
    wcel
    @20
    cW
    c.le
    wbr
    wn
    wa
    #
    @21
    cA
    wcel
    @21
    cW
    c.le
    wbr
    wn
    wa
    #
    @20
    @21
    wne
    #
    @12
    @20
    @21
    c.or
    co
    c.le
    wbr
    #
    wn
    @12
    @25
    wceq
    @28
    @31
    @19
    @0
    @9
    @3
    @35
    @28
    @32
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
    ltrnel
    syl3anc
    @19
    @0
    @9
    @6
    @36
    @28
    @32
    @30
    cA
    cQ
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
    @19
    @0
    @9
    @1
    @4
    @11
    @37
    @28
    @32
    @1
    @2
    @0
    @6
    @10
    @18
    simp12l
    @4
    @5
    @0
    @3
    @10
    @18
    simp13l
    @33
    cA
    cP
    cQ
    cT
    cG
    cH
    cK
    cW
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    ltrn11at
    syl113anc
    @19
    @38
    @14
    @7
    @10
    @11
    @15
    @17
    simp32
    @19
    @0
    @3
    @6
    @10
    @38
    @14
    wb
    @28
    @29
    @30
    @7
    @10
    @18
    simp2
    cA
    cP
    cQ
    cR
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
    cdlemg12b.r
    cdlemg10c
    syl121anc
    mtbird
    cA
    @20
    @21
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
    trlval4
    syl132anc
    oveq1d
    3brtr4d
end
