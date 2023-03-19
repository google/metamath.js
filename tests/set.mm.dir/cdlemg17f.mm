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
include "cdlemg17e.mm"
include "simp11.mm"
include "simp22.mm"
include "simp21.mm"
include "simp12.mm"
include "ltrnel.mm"
include "syl3anc.mm"
include "trlval2.mm"
include "oveq2d.mm"
include "simp12l.mm"
include "ltrncoat.mm"
include "syl121anc.mm"
include "eqid.mm"
include "cdleme0cp.mm"
include "syl12anc.mm"
include "3eqtrd.mm"

theorem cdlemg17f
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T /\ P =/= Q ) /\ ( ( G ` P ) =/= P /\ ( R ` G ) .<_ ( P .\/ Q ) /\ -. E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> ( ( F ` P ) .\/ ( F ` Q ) ) = ( ( F ` P ) .\/ ( G ` ( F ` P ) ) ) )

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
    @14
    @10
    c.or
    co
    @14
    @14
    @14
    cG
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    @16
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
    cdlemg17e
    @13
    @10
    @17
    @14
    c.or
    @13
    @0
    @7
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
    @10
    @17
    wceq
    @0
    @3
    @4
    @9
    @12
    simp11
    #
    @5
    @6
    @7
    @8
    @12
    simp22
    #
    @13
    @0
    @6
    @3
    @19
    @20
    @5
    @6
    @7
    @8
    @12
    simp21
    #
    @0
    @3
    @4
    @9
    @12
    simp12
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
    cA
    @14
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
    oveq2d
    @13
    @0
    @19
    @15
    cA
    wcel
    #
    @18
    @16
    wceq
    @20
    @23
    @13
    @0
    @7
    @6
    @1
    @24
    @20
    @21
    @22
    @1
    @2
    @0
    @4
    @9
    @12
    simp12l
    cA
    cP
    cT
    cG
    cF
    cH
    cK
    c.le
    cW
    cdlemg12.l
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    ltrncoat
    syl121anc
    cA
    @14
    @15
    @17
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
    @17
    eqid
    cdleme0cp
    syl12anc
    3eqtrd
end
