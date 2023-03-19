include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cfv.mm"
include "simp1.mm"
include "simp32.mm"
include "simp2l.mm"
include "ltrnel.mm"
include "syl3anc.mm"
include "simp2r.mm"
include "cdlemg7fvbwN.mm"
include "simp31.mm"
include "simp33.mm"
include "cdlemg2fv.mm"
include "syl122anc.mm"
include "oveq1d.mm"
include "simp2rl.mm"
include "lhpelim.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "eqtr4d.mm"

theorem cdlemg7fvN
  let cA: class A
  let cB: class B
  let cP: class P
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  assume cdlemg7fv.b: |- B = ( Base ` K )
  assume cdlemg7fv.l: |- .<_ = ( le ` K )
  assume cdlemg7fv.j: |- .\/ = ( join ` K )
  assume cdlemg7fv.m: |- ./\ = ( meet ` K )
  assume cdlemg7fv.a: |- A = ( Atoms ` K )
  assume cdlemg7fv.h: |- H = ( LHyp ` K )
  assume cdlemg7fv.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( X e. B /\ -. X .<_ W ) ) /\ ( F e. T /\ G e. T /\ ( P .\/ ( X ./\ W ) ) = X ) ) -> ( F ` ( G ` X ) ) = ( ( F ` ( G ` P ) ) .\/ ( X ./\ W ) ) )

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
    cX
    cB
    wcel
    #
    cX
    cW
    c.le
    wbr
    wn
    #
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
    cX
    cW
    c.an
    co
    #
    c.or
    co
    cX
    wceq
    #
    w3a
    #
    w3a
    #
    cX
    cG
    cfv
    #
    cF
    cfv
    #
    cP
    cG
    cfv
    #
    cF
    cfv
    #
    @12
    cW
    c.an
    co
    #
    c.or
    co
    #
    @15
    @8
    c.or
    co
    @11
    @0
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
    @12
    cB
    wcel
    @12
    cW
    c.le
    wbr
    wn
    wa
    #
    @6
    @14
    @16
    c.or
    co
    #
    @12
    wceq
    @13
    @17
    wceq
    @0
    @5
    @10
    simp1
    #
    @11
    @0
    @7
    @1
    @18
    @21
    @0
    @5
    @6
    @7
    @9
    simp32
    #
    @0
    @1
    @4
    @10
    simp2l
    #
    cA
    cP
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemg7fv.l
    cdlemg7fv.a
    cdlemg7fv.h
    cdlemg7fv.t
    ltrnel
    syl3anc
    #
    @11
    @0
    @4
    @7
    @19
    @21
    @0
    @1
    @4
    @10
    simp2r
    #
    @22
    cA
    cB
    cT
    cG
    cH
    cK
    c.le
    cW
    cX
    cdlemg7fv.l
    cdlemg7fv.a
    cdlemg7fv.h
    cdlemg7fv.t
    cdlemg7fv.b
    cdlemg7fvbwN
    syl3anc
    @0
    @5
    @6
    @7
    @9
    simp31
    @11
    @20
    @14
    @8
    c.or
    co
    #
    @12
    @11
    @16
    @8
    @14
    c.or
    @11
    @16
    @26
    cW
    c.an
    co
    #
    @8
    @11
    @12
    @26
    cW
    c.an
    @11
    @0
    @1
    @4
    @7
    @9
    @12
    @26
    wceq
    @21
    @23
    @25
    @22
    @0
    @5
    @6
    @7
    @9
    simp33
    cA
    cB
    cP
    cT
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cX
    cdlemg7fv.h
    cdlemg7fv.t
    cdlemg7fv.l
    cdlemg7fv.j
    cdlemg7fv.a
    cdlemg7fv.m
    cdlemg7fv.b
    cdlemg2fv
    syl122anc
    #
    oveq1d
    @11
    @0
    @18
    @2
    @27
    @8
    wceq
    @21
    @24
    @2
    @3
    @1
    @0
    @10
    simp2rl
    cA
    cB
    @14
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cX
    cdlemg7fv.b
    cdlemg7fv.l
    cdlemg7fv.j
    cdlemg7fv.m
    cdlemg7fv.a
    cdlemg7fv.h
    lhpelim
    syl3anc
    eqtrd
    #
    oveq2d
    @28
    eqtr4d
    cA
    cB
    @14
    cT
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    @12
    cdlemg7fv.h
    cdlemg7fv.t
    cdlemg7fv.l
    cdlemg7fv.j
    cdlemg7fv.a
    cdlemg7fv.m
    cdlemg7fv.b
    cdlemg2fv
    syl122anc
    @11
    @16
    @8
    @15
    c.or
    @29
    oveq2d
    eqtrd
end
