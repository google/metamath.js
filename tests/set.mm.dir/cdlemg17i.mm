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
include "simp22.mm"
include "simp12.mm"
include "simp21.mm"
include "ltrnel.mm"
include "syl3anc.mm"
include "simp31.mm"
include "ltrnatneq.mm"
include "syl131anc.mm"
include "neneqd.mm"
include "wo.mm"
include "simp1.mm"
include "jca.mm"
include "simp23.mm"
include "cdlemg17g.mm"
include "simp3.mm"
include "cdlemg17h.mm"
include "ord.mm"
include "mpd.mm"

theorem cdlemg17i
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T /\ P =/= Q ) /\ ( ( G ` P ) =/= P /\ ( R ` G ) .<_ ( P .\/ Q ) /\ -. E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> ( G ` ( F ` P ) ) = ( F ` Q ) )

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
    cP
    wne
    #
    cG
    cR
    cfv
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
    cP
    @10
    c.or
    co
    cQ
    @10
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
    cG
    cfv
    #
    @14
    wceq
    #
    wn
    @15
    cQ
    cF
    cfv
    #
    wceq
    #
    @13
    @15
    @14
    @13
    @0
    @5
    @1
    @14
    cA
    wcel
    @14
    cW
    c.le
    wbr
    wn
    wa
    #
    @8
    @15
    @14
    wne
    @0
    @1
    @2
    @7
    @12
    simp11
    #
    @3
    @4
    @5
    @6
    @12
    simp22
    #
    @0
    @1
    @2
    @7
    @12
    simp12
    #
    @13
    @0
    @4
    @1
    @19
    @20
    @3
    @4
    @5
    @6
    @12
    simp21
    #
    @22
    cA
    cP
    cT
    cF
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
    @3
    @7
    @8
    @9
    @11
    simp31
    cA
    cP
    @14
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
    ltrnatneq
    syl131anc
    neneqd
    @13
    @16
    @18
    @13
    @3
    @15
    cA
    wcel
    @15
    cW
    c.le
    wbr
    wn
    wa
    #
    @4
    @5
    wa
    @6
    @15
    @14
    @17
    c.or
    co
    c.le
    wbr
    #
    wa
    @12
    @16
    @18
    wo
    @3
    @7
    @12
    simp1
    @13
    @0
    @5
    @19
    @25
    @20
    @21
    @24
    cA
    @14
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
    @13
    @4
    @5
    @23
    @21
    jca
    @13
    @6
    @26
    @3
    @4
    @5
    @6
    @12
    simp23
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
    cdlemg17g
    jca
    @3
    @7
    @12
    simp3
    cA
    cP
    cQ
    cR
    @15
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
    cdlemg17h
    syl131anc
    ord
    mpd
end
