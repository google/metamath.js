include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "simp11.mm"
include "simp12.mm"
include "jca.mm"
include "simp21.mm"
include "simp22.mm"
include "simp13l.mm"
include "simp13r.mm"
include "simp23.mm"
include "simp33.mm"
include "simp31.mm"
include "simp32.mm"
include "cdlemg17pq.mm"
include "syl333anc.mm"
include "cdlemg17i.mm"
include "syl.mm"

theorem cdlemg17iqN
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
  let cS: class S
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
  disjoint F r
  disjoint S r
  assert |- ( ( ( K e. HL /\ W e. H /\ ( F e. T /\ G e. T ) ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ P =/= Q ) /\ ( ( R ` G ) .<_ ( P .\/ Q ) /\ -. E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) /\ ( G ` P ) =/= P ) ) -> ( G ` ( F ` Q ) ) = ( F ` P ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
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
    cP
    cQ
    wne
    #
    w3a
    #
    cG
    cR
    cfv
    #
    cP
    cQ
    c.or
    co
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
    #
    cP
    @12
    c.or
    co
    #
    cQ
    @12
    c.or
    co
    #
    wceq
    wa
    vr
    cA
    wrex
    wn
    #
    cP
    cG
    cfv
    cP
    wne
    #
    w3a
    #
    w3a
    #
    @0
    @1
    wa
    #
    @7
    @6
    w3a
    @2
    @3
    cQ
    cP
    wne
    w3a
    cQ
    cG
    cfv
    cQ
    wne
    @10
    cQ
    cP
    c.or
    co
    c.le
    wbr
    @13
    @15
    @14
    wceq
    wa
    vr
    cA
    wrex
    wn
    w3a
    w3a
    #
    cQ
    cF
    cfv
    cG
    cfv
    cP
    cF
    cfv
    wceq
    @19
    @20
    @6
    @7
    @2
    @3
    @8
    @17
    @11
    @16
    @21
    @19
    @0
    @1
    @0
    @1
    @4
    @9
    @18
    simp11
    @0
    @1
    @4
    @9
    @18
    simp12
    jca
    @5
    @6
    @7
    @8
    @18
    simp21
    @5
    @6
    @7
    @8
    @18
    simp22
    @2
    @3
    @0
    @1
    @9
    @18
    simp13l
    @2
    @3
    @0
    @1
    @9
    @18
    simp13r
    @5
    @6
    @7
    @8
    @18
    simp23
    @5
    @9
    @11
    @16
    @17
    simp33
    @5
    @9
    @11
    @16
    @17
    simp31
    @5
    @9
    @11
    @16
    @17
    simp32
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
    vr
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg17pq
    syl333anc
    cA
    cQ
    cP
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
    vr
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg17i
    syl
end
