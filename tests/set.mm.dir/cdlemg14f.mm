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
include "simp32.mm"
include "simp2l.mm"
include "simp2r.mm"
include "ltrnu.mm"
include "syl211anc.mm"
include "simp31.mm"
include "ltrnel.mm"
include "syl3anc.mm"
include "simp33.mm"
include "ltrnateq.mm"
include "syl131anc.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"

theorem cdlemg14f
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T /\ ( F ` P ) = P ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ W ) = ( ( Q .\/ ( F ` ( G ` Q ) ) ) ./\ W ) )

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
    cF
    cfv
    cP
    wceq
    #
    w3a
    #
    w3a
    #
    cP
    cP
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
    cQ
    cQ
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
    cP
    @9
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
    @12
    cF
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    @8
    @0
    @5
    @1
    @2
    @11
    @14
    wceq
    @0
    @3
    @7
    simp1
    #
    @0
    @3
    @4
    @5
    @6
    simp32
    #
    @0
    @1
    @2
    @7
    simp2l
    #
    @0
    @1
    @2
    @7
    simp2r
    #
    cA
    cP
    cQ
    cT
    cG
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
    @8
    @16
    @10
    cW
    c.an
    @8
    @15
    @9
    cP
    c.or
    @8
    @0
    @4
    @1
    @9
    cA
    wcel
    @9
    cW
    c.le
    wbr
    wn
    wa
    #
    @6
    @15
    @9
    wceq
    @19
    @0
    @3
    @4
    @5
    @6
    simp31
    #
    @21
    @8
    @0
    @5
    @1
    @23
    @19
    @20
    @21
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
    @0
    @3
    @4
    @5
    @6
    simp33
    #
    cA
    cP
    @9
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
    ltrnateq
    syl131anc
    oveq2d
    oveq1d
    @8
    @18
    @13
    cW
    c.an
    @8
    @17
    @12
    cQ
    c.or
    @8
    @0
    @4
    @1
    @12
    cA
    wcel
    @12
    cW
    c.le
    wbr
    wn
    wa
    #
    @6
    @17
    @12
    wceq
    @19
    @24
    @21
    @8
    @0
    @5
    @2
    @26
    @19
    @20
    @22
    cA
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
    ltrnel
    syl3anc
    @25
    cA
    cP
    @12
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
    ltrnateq
    syl131anc
    oveq2d
    oveq1d
    3eqtr4d
end
