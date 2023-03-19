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
include "simp21.mm"
include "simp22.mm"
include "simp31.mm"
include "simp32.mm"
include "cdlemg4c.mm"
include "syl131anc.mm"
include "simp1l.mm"
include "simp21l.mm"
include "ltrnel.mm"
include "simpld.mm"
include "syl3anc.mm"
include "hlatjcom.mm"
include "cdlemg4b1.mm"
include "simp33.mm"
include "oveq2d.mm"
include "3eqtr4rd.mm"
include "breq2d.mm"
include "mtbird.mm"

theorem cdlemg4d
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ F e. T ) /\ ( G e. T /\ -. Q .<_ ( P .\/ V ) /\ ( F ` ( G ` P ) ) = P ) ) -> -. ( G ` Q ) .<_ ( ( G ` P ) .\/ ( F ` ( G ` P ) ) ) )

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
    cQ
    cG
    cfv
    #
    @12
    @13
    c.or
    co
    #
    c.le
    wbr
    @17
    @10
    c.le
    wbr
    #
    @16
    @2
    @5
    @6
    @9
    @11
    @19
    wn
    @2
    @8
    @15
    simp1
    #
    @2
    @5
    @6
    @7
    @15
    simp21
    #
    @2
    @5
    @6
    @7
    @15
    simp22
    @2
    @8
    @9
    @11
    @14
    simp31
    #
    @2
    @8
    @9
    @11
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
    cV
    cW
    cdlemg4.l
    cdlemg4.a
    cdlemg4.h
    cdlemg4.t
    cdlemg4.r
    cdlemg4.j
    cdlemg4b.v
    cdlemg4c
    syl131anc
    @16
    @18
    @10
    @17
    c.le
    @16
    cP
    @12
    c.or
    co
    #
    @12
    cP
    c.or
    co
    #
    @10
    @18
    @16
    @0
    @3
    @12
    cA
    wcel
    #
    @23
    @24
    wceq
    @0
    @1
    @8
    @15
    simp1l
    @3
    @4
    @6
    @7
    @2
    @15
    simp21l
    @16
    @2
    @9
    @5
    @25
    @20
    @22
    @21
    @2
    @9
    @5
    w3a
    @25
    @12
    cW
    c.le
    wbr
    wn
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
    simpld
    syl3anc
    cA
    c.or
    cK
    cP
    @12
    cdlemg4.j
    cdlemg4.a
    hlatjcom
    syl3anc
    @16
    @2
    @5
    @9
    @10
    @23
    wceq
    @20
    @21
    @22
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
    @16
    @13
    cP
    @12
    c.or
    @2
    @8
    @9
    @11
    @14
    simp33
    oveq2d
    3eqtr4rd
    breq2d
    mtbird
end
