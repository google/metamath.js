include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp21.mm"
include "eqid.mm"
include "cdlemg2k.mm"
include "syl121anc.mm"
include "simp22.mm"
include "trlval2.mm"
include "syl3anc.mm"
include "simp1.mm"
include "simp23.mm"
include "simp31.mm"
include "simp32.mm"
include "simp33.mm"
include "cdlemg17b.mm"
include "syl123anc.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "eqtr4d.mm"

theorem cdlemg17e
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
  let vr: setvar r
  assume cdlemg12.l: |- .<_ = ( le ` K )
  assume cdlemg12.j: |- .\/ = ( join ` K )
  assume cdlemg12.m: |- ./\ = ( meet ` K )
  assume cdlemg12.a: |- A = ( Atoms ` K )
  assume cdlemg12.h: |- H = ( LHyp ` K )
  assume cdlemg12.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg12b.r: |- R = ( ( trL ` K ) ` W )

  disjoint A r
  disjoint G r
  disjoint .\/ r
  disjoint .<_ r
  disjoint P r
  disjoint Q r
  disjoint W r
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T /\ P =/= Q ) /\ ( ( G ` P ) =/= P /\ ( R ` G ) .<_ ( P .\/ Q ) /\ -. E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> ( ( F ` P ) .\/ ( F ` Q ) ) = ( ( F ` P ) .\/ ( R ` G ) ) )

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
    cP
    cW
    c.le
    wbr
    wn
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
    cP
    cQ
    wne
    #
    w3a
    #
    cP
    cG
    cfv
    #
    cP
    wne
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
    vr
    cv
    #
    cW
    c.le
    wbr
    wn
    cP
    @13
    c.or
    co
    cQ
    @13
    c.or
    co
    wceq
    wa
    vr
    cA
    wrex
    wn
    #
    w3a
    #
    w3a
    #
    cP
    cF
    cfv
    #
    cQ
    cF
    cfv
    c.or
    co
    #
    @17
    @11
    cW
    c.an
    co
    #
    c.or
    co
    #
    @17
    @10
    c.or
    co
    @16
    @0
    @1
    @2
    @4
    @18
    @20
    wceq
    @0
    @1
    @2
    @7
    @15
    simp11
    #
    @0
    @1
    @2
    @7
    @15
    simp12
    #
    @0
    @1
    @2
    @7
    @15
    simp13
    @3
    @4
    @5
    @6
    @15
    simp21
    cA
    cP
    cQ
    cT
    @19
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg12.h
    cdlemg12.t
    cdlemg12.l
    cdlemg12.j
    cdlemg12.a
    cdlemg12.m
    @19
    eqid
    cdlemg2k
    syl121anc
    @16
    @10
    @19
    @17
    c.or
    @16
    @10
    cP
    @8
    c.or
    co
    #
    cW
    c.an
    co
    #
    @19
    @16
    @0
    @5
    @1
    @10
    @24
    wceq
    @21
    @3
    @4
    @5
    @6
    @15
    simp22
    #
    @22
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
    @16
    @23
    @11
    cW
    c.an
    @16
    @8
    cQ
    cP
    c.or
    @16
    @3
    @5
    @6
    @9
    @12
    @14
    @8
    cQ
    wceq
    @3
    @7
    @15
    simp1
    @25
    @3
    @4
    @5
    @6
    @15
    simp23
    @3
    @7
    @9
    @12
    @14
    simp31
    @3
    @7
    @9
    @12
    @14
    simp32
    @3
    @7
    @9
    @12
    @14
    simp33
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
    vr
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg17b
    syl123anc
    oveq2d
    oveq1d
    eqtrd
    oveq2d
    eqtr4d
end
