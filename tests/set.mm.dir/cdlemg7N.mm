include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "simpl1.mm"
include "simpl31.mm"
include "simpl32.mm"
include "simpl2r.mm"
include "ltrncl.mm"
include "syl3anc.mm"
include "simpr.mm"
include "ltrnval1.mm"
include "syl112anc.mm"
include "eqbrtrd.mm"
include "eqtrd.mm"
include "simpl2l.mm"
include "jca.mm"
include "simpl33.mm"
include "cdlemg7aN.mm"
include "syl123anc.mm"
include "pm2.61dan.mm"

theorem cdlemg7N
  let cA: class A
  let cB: class B
  let cP: class P
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let vr: setvar r
  assume cdlemg7.b: |- B = ( Base ` K )
  assume cdlemg7.l: |- .<_ = ( le ` K )
  assume cdlemg7.a: |- A = ( Atoms ` K )
  assume cdlemg7.h: |- H = ( LHyp ` K )
  assume cdlemg7.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ X e. B ) /\ ( F e. T /\ G e. T /\ ( F ` ( G ` P ) ) = P ) ) -> ( F ` ( G ` X ) ) = X )

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
    cF
    cfv
    cP
    wceq
    #
    w3a
    #
    w3a
    #
    cX
    cW
    c.le
    wbr
    #
    cX
    cG
    cfv
    #
    cF
    cfv
    #
    cX
    wceq
    #
    @8
    @9
    wa
    #
    @11
    @10
    cX
    @13
    @0
    @4
    @10
    cB
    wcel
    #
    @10
    cW
    c.le
    wbr
    @11
    @10
    wceq
    @0
    @3
    @7
    @9
    simpl1
    #
    @4
    @5
    @6
    @0
    @3
    @9
    simpl31
    @13
    @0
    @5
    @2
    @14
    @15
    @4
    @5
    @6
    @0
    @3
    @9
    simpl32
    #
    @1
    @2
    @0
    @7
    @9
    simpl2r
    #
    cB
    cT
    cG
    cH
    cK
    chlt
    cW
    cX
    cdlemg7.b
    cdlemg7.h
    cdlemg7.t
    ltrncl
    syl3anc
    @13
    @10
    cX
    cW
    c.le
    @13
    @0
    @5
    @2
    @9
    @10
    cX
    wceq
    @15
    @16
    @17
    @8
    @9
    simpr
    #
    cB
    cT
    cG
    cH
    cK
    c.le
    chlt
    cW
    cX
    cdlemg7.b
    cdlemg7.l
    cdlemg7.h
    cdlemg7.t
    ltrnval1
    syl112anc
    #
    @18
    eqbrtrd
    cB
    cT
    cF
    cH
    cK
    c.le
    chlt
    cW
    @10
    cdlemg7.b
    cdlemg7.l
    cdlemg7.h
    cdlemg7.t
    ltrnval1
    syl112anc
    @19
    eqtrd
    @8
    @9
    wn
    #
    wa
    #
    @0
    @1
    @2
    @20
    wa
    @4
    @5
    @6
    @12
    @0
    @3
    @7
    @20
    simpl1
    @1
    @2
    @0
    @7
    @20
    simpl2l
    @21
    @2
    @20
    @1
    @2
    @0
    @7
    @20
    simpl2r
    @8
    @20
    simpr
    jca
    @4
    @5
    @6
    @0
    @3
    @20
    simpl31
    @4
    @5
    @6
    @0
    @3
    @20
    simpl32
    @4
    @5
    @6
    @0
    @3
    @20
    simpl33
    cA
    cB
    cP
    cT
    cF
    cG
    cH
    cK
    c.le
    cW
    cX
    cdlemg7.b
    cdlemg7.l
    cdlemg7.a
    cdlemg7.h
    cdlemg7.t
    cdlemg7aN
    syl123anc
    pm2.61dan
end
