include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "simp3l.mm"
include "oveq2d.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp3r.mm"
include "trljat3.mm"
include "syl3anc.mm"
include "simp2r.mm"
include "trljat1.mm"
include "3eqtr3rd.mm"

theorem cdlemk1
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let cW: class W
  assume cdlemk.b: |- B = ( Base ` K )
  assume cdlemk.l: |- .<_ = ( le ` K )
  assume cdlemk.j: |- .\/ = ( join ` K )
  assume cdlemk.a: |- A = ( Atoms ` K )
  assume cdlemk.h: |- H = ( LHyp ` K )
  assume cdlemk.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ N e. T ) /\ ( ( R ` F ) = ( R ` N ) /\ ( P e. A /\ -. P .<_ W ) ) ) -> ( P .\/ ( N ` P ) ) = ( ( F ` P ) .\/ ( R ` F ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cT
    wcel
    #
    cN
    cT
    wcel
    #
    wa
    #
    cF
    cR
    cfv
    #
    cN
    cR
    cfv
    #
    wceq
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
    wa
    #
    w3a
    #
    cP
    @4
    c.or
    co
    #
    cP
    @5
    c.or
    co
    #
    cP
    cF
    cfv
    @4
    c.or
    co
    #
    cP
    cP
    cN
    cfv
    c.or
    co
    #
    @9
    @4
    @5
    cP
    c.or
    @0
    @3
    @6
    @7
    simp3l
    oveq2d
    @9
    @0
    @1
    @7
    @10
    @12
    wceq
    @0
    @3
    @8
    simp1
    #
    @0
    @1
    @2
    @8
    simp2l
    @0
    @3
    @6
    @7
    simp3r
    #
    cA
    cP
    cR
    cT
    cF
    cH
    c.or
    cK
    c.le
    cW
    cdlemk.l
    cdlemk.j
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    trljat3
    syl3anc
    @9
    @0
    @2
    @7
    @11
    @13
    wceq
    @14
    @0
    @1
    @2
    @8
    simp2r
    @15
    cA
    cP
    cR
    cT
    cN
    cH
    c.or
    cK
    c.le
    cW
    cdlemk.l
    cdlemk.j
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    trljat1
    syl3anc
    3eqtr3rd
end
