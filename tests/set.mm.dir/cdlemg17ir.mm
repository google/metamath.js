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
include "simp1.mm"
include "simp22.mm"
include "simp23.mm"
include "simp3.mm"
include "cdlemg17b.mm"
include "syl121anc.mm"
include "fveq2d.mm"

theorem cdlemg17ir
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T /\ P =/= Q ) /\ ( ( G ` P ) =/= P /\ ( R ` G ) .<_ ( P .\/ Q ) /\ -. E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> ( F ` ( G ` P ) ) = ( F ` Q ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
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
    cG
    cR
    cfv
    cP
    cQ
    c.or
    co
    c.le
    wbr
    vr
    cv
    #
    cW
    c.le
    wbr
    wn
    cP
    @6
    c.or
    co
    cQ
    @6
    c.or
    co
    wceq
    wa
    vr
    cA
    wrex
    wn
    w3a
    #
    w3a
    #
    @5
    cQ
    cF
    @8
    @0
    @2
    @3
    @7
    @5
    cQ
    wceq
    @0
    @4
    @7
    simp1
    @0
    @1
    @2
    @3
    @7
    simp22
    @0
    @1
    @2
    @3
    @7
    simp23
    @0
    @4
    @7
    simp3
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
    syl121anc
    fveq2d
end
