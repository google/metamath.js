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
include "simp21r.mm"
include "simp12.mm"
include "cdlemg18d.mm"
include "simp23.mm"
include "simp1.mm"
include "simp21l.mm"
include "simp22.mm"
include "simp31.mm"
include "simp33.mm"
include "cdlemg17.mm"
include "syl133anc.mm"
include "ltrnatlw.mm"
include "syl132anc.mm"

theorem cdlemg18
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( F e. T /\ G e. T ) /\ P =/= Q /\ ( G ` P ) =/= P ) /\ ( ( R ` G ) .<_ ( P .\/ Q ) /\ ( ( F ` ( G ` P ) ) .\/ ( F ` ( G ` Q ) ) ) =/= ( P .\/ Q ) /\ -. E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ ( Q .\/ ( F ` ( G ` Q ) ) ) ) .<_ W )

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
    wa
    #
    cP
    cQ
    wne
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
    cG
    cR
    cfv
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    @8
    cF
    cfv
    #
    cQ
    cG
    cfv
    cF
    cfv
    #
    c.or
    co
    @11
    wne
    #
    vr
    cv
    #
    cW
    c.le
    wbr
    wn
    cP
    @16
    c.or
    co
    cQ
    @16
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
    @0
    @5
    @1
    cP
    @13
    c.or
    co
    cQ
    @14
    c.or
    co
    c.an
    co
    #
    cA
    wcel
    @9
    @20
    cG
    cfv
    @20
    wceq
    #
    @20
    cW
    c.le
    wbr
    @0
    @1
    @2
    @10
    @18
    simp11
    @4
    @5
    @7
    @9
    @3
    @18
    simp21r
    #
    @0
    @1
    @2
    @10
    @18
    simp12
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
    cdlemg18d
    @3
    @6
    @7
    @9
    @18
    simp23
    #
    @19
    @3
    @4
    @5
    @7
    @9
    @12
    @17
    @21
    @3
    @10
    @18
    simp1
    @4
    @5
    @7
    @9
    @3
    @18
    simp21l
    @22
    @3
    @6
    @7
    @9
    @18
    simp22
    @23
    @3
    @10
    @12
    @15
    @17
    simp31
    @3
    @10
    @12
    @15
    @17
    simp33
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
    cdlemg17
    syl133anc
    cA
    cP
    @20
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
    ltrnatlw
    syl132anc
end
