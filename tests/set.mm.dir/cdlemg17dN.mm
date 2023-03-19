include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "simp1.mm"
include "simp21.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simpr.mm"
include "trlval2.mm"
include "syl211anc.mm"
include "syl2anc.mm"
include "simp11.mm"
include "simp12.mm"
include "jca.mm"
include "simp22.mm"
include "simp13.mm"
include "simp23.mm"
include "simp33.mm"
include "simp31.mm"
include "simp32.mm"
include "cdlemg17b.mm"
include "syl323anc.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem cdlemg17dN
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
  assert |- ( ( ( K e. HL /\ W e. H /\ G e. T ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ P =/= Q ) /\ ( ( R ` G ) .<_ ( P .\/ Q ) /\ -. E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) /\ ( G ` P ) =/= P ) ) -> ( R ` G ) = ( ( P .\/ Q ) ./\ W ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    cG
    cT
    wcel
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
    @11
    c.or
    co
    cQ
    @11
    c.or
    co
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
    #
    cP
    wne
    #
    w3a
    #
    w3a
    #
    @8
    cP
    @13
    c.or
    co
    #
    cW
    c.an
    co
    #
    @9
    cW
    c.an
    co
    @16
    @3
    @4
    @8
    @18
    wceq
    #
    @3
    @7
    @15
    simp1
    @3
    @4
    @5
    @6
    @15
    simp21
    #
    @3
    @4
    wa
    @0
    @1
    @2
    @4
    @19
    @0
    @1
    @2
    @4
    simpl1
    @0
    @1
    @2
    @4
    simpl2
    @0
    @1
    @2
    @4
    simpl3
    @3
    @4
    simpr
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
    syl211anc
    syl2anc
    @16
    @17
    @9
    cW
    c.an
    @16
    @13
    cQ
    cP
    c.or
    @16
    @0
    @1
    wa
    @4
    @5
    @2
    @6
    @14
    @10
    @12
    @13
    cQ
    wceq
    @16
    @0
    @1
    @0
    @1
    @2
    @7
    @15
    simp11
    @0
    @1
    @2
    @7
    @15
    simp12
    jca
    @20
    @3
    @4
    @5
    @6
    @15
    simp22
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
    simp23
    @3
    @7
    @10
    @12
    @14
    simp33
    @3
    @7
    @10
    @12
    @14
    simp31
    @3
    @7
    @10
    @12
    @14
    simp32
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
    syl323anc
    oveq2d
    oveq1d
    eqtrd
end
