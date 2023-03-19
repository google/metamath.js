include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "co.mm"
include "simp1.mm"
include "simp31.mm"
include "simp2l.mm"
include "simp2r.mm"
include "ltrnu.mm"
include "syl211anc.mm"
include "simp33.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "simp32.mm"
include "ltrnateq.mm"
include "syl131anc.mm"
include "3eqtr4d.mm"

theorem cdlemg14g
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T /\ ( G ` P ) = P ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ W ) = ( ( Q .\/ ( F ` ( G ` Q ) ) ) ./\ W ) )

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
    wa
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
    cG
    cfv
    #
    cP
    wceq
    #
    w3a
    #
    w3a
    #
    cP
    cP
    cF
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    #
    cQ
    cQ
    cF
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    #
    cP
    @6
    cF
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    cQ
    cQ
    cG
    cfv
    #
    cF
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    @9
    @0
    @4
    @1
    @2
    @12
    @15
    wceq
    @0
    @3
    @8
    simp1
    #
    @0
    @3
    @4
    @5
    @7
    simp31
    @0
    @1
    @2
    @8
    simp2l
    #
    @0
    @1
    @2
    @8
    simp2r
    #
    cA
    cP
    cQ
    cT
    cF
    cH
    c.or
    cK
    c.le
    c.an
    chlt
    cW
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    ltrnu
    syl211anc
    @9
    @17
    @11
    cW
    c.an
    @9
    @16
    @10
    cP
    c.or
    @9
    @6
    cP
    cF
    @0
    @3
    @4
    @5
    @7
    simp33
    #
    fveq2d
    oveq2d
    oveq1d
    @9
    @20
    @14
    cW
    c.an
    @9
    @19
    @13
    cQ
    c.or
    @9
    @18
    cQ
    cF
    @9
    @0
    @5
    @1
    @2
    @7
    @18
    cQ
    wceq
    @21
    @0
    @3
    @4
    @5
    @7
    simp32
    @22
    @23
    @24
    cA
    cP
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
    ltrnateq
    syl131anc
    fveq2d
    oveq2d
    oveq1d
    3eqtr4d
end
