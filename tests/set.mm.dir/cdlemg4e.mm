include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "simp1.mm"
include "simp23.mm"
include "simp31.mm"
include "simp21.mm"
include "ltrnel.mm"
include "syl3anc.mm"
include "simp22.mm"
include "cdlemg4d.mm"
include "cdlemc.mm"
include "syl131anc.mm"

theorem cdlemg4e
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
  assume cdlemg4.m: |- ./\ = ( meet ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ F e. T ) /\ ( G e. T /\ -. Q .<_ ( P .\/ V ) /\ ( F ` ( G ` P ) ) = P ) ) -> ( F ` ( G ` Q ) ) = ( ( ( G ` Q ) .\/ ( R ` F ) ) ./\ ( ( F ` ( G ` P ) ) .\/ ( ( ( G ` P ) .\/ ( G ` Q ) ) ./\ W ) ) ) )

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
    c.le
    wbr
    wn
    #
    cP
    cG
    cfv
    #
    cF
    cfv
    #
    cP
    wceq
    #
    w3a
    #
    w3a
    #
    @0
    @3
    @7
    cA
    wcel
    @7
    cW
    c.le
    wbr
    wn
    wa
    #
    cQ
    cG
    cfv
    #
    cA
    wcel
    @13
    cW
    c.le
    wbr
    wn
    wa
    #
    @13
    @7
    @8
    c.or
    co
    c.le
    wbr
    wn
    @13
    cF
    cfv
    @13
    cF
    cR
    cfv
    c.or
    co
    @8
    @7
    @13
    c.or
    co
    cW
    c.an
    co
    c.or
    co
    c.an
    co
    wceq
    @0
    @4
    @10
    simp1
    #
    @0
    @1
    @2
    @3
    @10
    simp23
    @11
    @0
    @5
    @1
    @12
    @15
    @0
    @4
    @5
    @6
    @9
    simp31
    #
    @0
    @1
    @2
    @3
    @10
    simp21
    cA
    cP
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemg4.l
    cdlemg4.a
    cdlemg4.h
    cdlemg4.t
    ltrnel
    syl3anc
    @11
    @0
    @5
    @2
    @14
    @15
    @16
    @0
    @1
    @2
    @3
    @10
    simp22
    cA
    cQ
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemg4.l
    cdlemg4.a
    cdlemg4.h
    cdlemg4.t
    ltrnel
    syl3anc
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
    cdlemg4.l
    cdlemg4.a
    cdlemg4.h
    cdlemg4.t
    cdlemg4.r
    cdlemg4.j
    cdlemg4b.v
    cdlemg4d
    cA
    @7
    @13
    cR
    cT
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg4.l
    cdlemg4.j
    cdlemg4.m
    cdlemg4.a
    cdlemg4.h
    cdlemg4.t
    cdlemg4.r
    cdlemc
    syl131anc
end
