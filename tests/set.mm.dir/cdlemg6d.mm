include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "simp1.mm"
include "simp21.mm"
include "simp31.mm"
include "cdlemg4b1.mm"
include "syl3anc.mm"
include "breq2d.mm"
include "notbid.mm"
include "anbi2d.mm"
include "cdlemg6c.mm"
include "sylbird.mm"

theorem cdlemg6d
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
  let cV: class V
  let cW: class W
  let vr: setvar r
  assume cdlemg4.l: |- .<_ = ( le ` K )
  assume cdlemg4.a: |- A = ( Atoms ` K )
  assume cdlemg4.h: |- H = ( LHyp ` K )
  assume cdlemg4.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg4.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemg4.j: |- .\/ = ( join ` K )
  assume cdlemg4b.v: |- V = ( R ` G )

  disjoint A r
  disjoint F r
  disjoint G r
  disjoint H r
  disjoint .\/ r
  disjoint K r
  disjoint .<_ r
  disjoint P r
  disjoint Q r
  disjoint T r
  disjoint V r
  disjoint W r
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ F e. T ) /\ ( G e. T /\ Q .<_ ( P .\/ V ) /\ ( F ` ( G ` P ) ) = P ) ) -> ( ( ( r e. A /\ -. r .<_ W ) /\ -. r .<_ ( P .\/ ( G ` P ) ) ) -> ( F ` ( G ` Q ) ) = Q ) )

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
    cQ
    cP
    cV
    c.or
    co
    #
    c.le
    wbr
    #
    cP
    cG
    cfv
    #
    cF
    cfv
    cP
    wceq
    #
    w3a
    #
    w3a
    #
    vr
    cv
    #
    cA
    wcel
    @12
    cW
    c.le
    wbr
    wn
    wa
    #
    @12
    cP
    @8
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    wa
    @13
    @12
    @6
    c.le
    wbr
    #
    wn
    #
    wa
    cQ
    cG
    cfv
    cF
    cfv
    cQ
    wceq
    @11
    @18
    @16
    @13
    @11
    @17
    @15
    @11
    @6
    @14
    @12
    c.le
    @11
    @0
    @1
    @5
    @6
    @14
    wceq
    @0
    @4
    @10
    simp1
    @0
    @1
    @2
    @3
    @10
    simp21
    @0
    @4
    @5
    @7
    @9
    simp31
    cA
    cP
    cR
    cT
    cG
    cH
    c.or
    cK
    c.le
    cV
    cW
    cdlemg4.l
    cdlemg4.a
    cdlemg4.h
    cdlemg4.t
    cdlemg4.r
    cdlemg4.j
    cdlemg4b.v
    cdlemg4b1
    syl3anc
    breq2d
    notbid
    anbi2d
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
    cV
    cW
    vr
    cdlemg4.l
    cdlemg4.a
    cdlemg4.h
    cdlemg4.t
    cdlemg4.r
    cdlemg4.j
    cdlemg4b.v
    cdlemg6c
    sylbird
end
