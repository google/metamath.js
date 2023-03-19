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
include "simp31.mm"
include "neneqd.mm"
include "wo.mm"
include "simp11l.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp2l.mm"
include "simp32.mm"
include "cdlemg17a.mm"
include "syl122anc.mm"
include "simp33.mm"
include "simp12l.mm"
include "simp13l.mm"
include "simp2r.mm"
include "ltrnel.mm"
include "syl3anc.mm"
include "cdleme0nex.mm"
include "syl331anc.mm"
include "ord.mm"
include "mpd.mm"

theorem cdlemg17b
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( G e. T /\ P =/= Q ) /\ ( ( G ` P ) =/= P /\ ( R ` G ) .<_ ( P .\/ Q ) /\ -. E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> ( G ` P ) = Q )

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
    w3a
    #
    cG
    cT
    wcel
    #
    cP
    cQ
    wne
    #
    wa
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
    @17
    c.or
    co
    cQ
    @17
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
    @13
    cP
    wceq
    #
    wn
    @13
    cQ
    wceq
    #
    @20
    @13
    cP
    @9
    @12
    @14
    @16
    @18
    simp31
    neneqd
    @20
    @21
    @22
    @20
    @0
    @13
    @15
    c.le
    wbr
    #
    @18
    @3
    @6
    @11
    @13
    cA
    wcel
    @13
    cW
    c.le
    wbr
    wn
    wa
    #
    @21
    @22
    wo
    @0
    @1
    @5
    @8
    @12
    @19
    simp11l
    @20
    @2
    @5
    @8
    @10
    @16
    @23
    @2
    @5
    @8
    @12
    @19
    simp11
    #
    @2
    @5
    @8
    @12
    @19
    simp12
    #
    @2
    @5
    @8
    @12
    @19
    simp13
    @9
    @10
    @11
    @19
    simp2l
    #
    @9
    @12
    @14
    @16
    @18
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
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg17a
    syl122anc
    @9
    @12
    @14
    @16
    @18
    simp33
    @3
    @4
    @2
    @8
    @12
    @19
    simp12l
    @6
    @7
    @2
    @5
    @12
    @19
    simp13l
    @9
    @10
    @11
    @19
    simp2r
    @20
    @2
    @10
    @5
    @24
    @25
    @27
    @26
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
    cA
    cP
    cQ
    @13
    c.or
    cK
    c.le
    cW
    vr
    cdlemg12.l
    cdlemg12.j
    cdlemg12.a
    cdleme0nex
    syl331anc
    ord
    mpd
end
