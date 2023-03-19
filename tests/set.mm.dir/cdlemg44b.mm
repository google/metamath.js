include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "wne.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl21.mm"
include "simpl23.mm"
include "simpl22.mm"
include "ltrnel.mm"
include "syl3anc.mm"
include "simpr.mm"
include "ltrnateq.mm"
include "syl131anc.mm"
include "fveq2d.mm"
include "eqtr4d.mm"
include "simpl2.mm"
include "simprl.mm"
include "simprr.mm"
include "simpl3.mm"
include "cdlemg44a.mm"
include "syl113anc.mm"
include "pm2.61da2ne.mm"

theorem cdlemg44b
  let cA: class A
  let cP: class P
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume cdlemg44.h: |- H = ( LHyp ` K )
  assume cdlemg44.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg44.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemg44.l: |- .<_ = ( le ` K )
  assume cdlemg44.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T /\ ( P e. A /\ -. P .<_ W ) ) /\ ( R ` F ) =/= ( R ` G ) ) -> ( F ` ( G ` P ) ) = ( G ` ( F ` P ) ) )

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
    cG
    cT
    wcel
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
    w3a
    #
    cF
    cR
    cfv
    cG
    cR
    cfv
    wne
    #
    w3a
    #
    cP
    cG
    cfv
    #
    cF
    cfv
    #
    cP
    cF
    cfv
    #
    cG
    cfv
    #
    wceq
    #
    @9
    cP
    @7
    cP
    @6
    @9
    cP
    wceq
    #
    wa
    #
    @8
    @7
    @10
    @13
    @0
    @1
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
    @12
    @8
    @7
    wceq
    @0
    @4
    @5
    @12
    simpl1
    #
    @1
    @2
    @3
    @0
    @5
    @12
    simpl21
    @1
    @2
    @3
    @0
    @5
    @12
    simpl23
    #
    @13
    @0
    @2
    @3
    @14
    @15
    @1
    @2
    @3
    @0
    @5
    @12
    simpl22
    @16
    cA
    cP
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemg44.l
    cdlemg44.a
    cdlemg44.h
    cdlemg44.t
    ltrnel
    syl3anc
    @6
    @12
    simpr
    #
    cA
    cP
    @7
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg44.l
    cdlemg44.a
    cdlemg44.h
    cdlemg44.t
    ltrnateq
    syl131anc
    @13
    @9
    cP
    cG
    @17
    fveq2d
    eqtr4d
    @6
    @7
    cP
    wceq
    #
    wa
    #
    @8
    @9
    @10
    @19
    @7
    cP
    cF
    @6
    @18
    simpr
    #
    fveq2d
    @19
    @0
    @2
    @3
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
    @18
    @10
    @9
    wceq
    @0
    @4
    @5
    @18
    simpl1
    #
    @1
    @2
    @3
    @0
    @5
    @18
    simpl22
    @1
    @2
    @3
    @0
    @5
    @18
    simpl23
    #
    @19
    @0
    @1
    @3
    @21
    @22
    @1
    @2
    @3
    @0
    @5
    @18
    simpl21
    @23
    cA
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg44.l
    cdlemg44.a
    cdlemg44.h
    cdlemg44.t
    ltrnel
    syl3anc
    @20
    cA
    cP
    @9
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemg44.l
    cdlemg44.a
    cdlemg44.h
    cdlemg44.t
    ltrnateq
    syl131anc
    eqtr4d
    @6
    @9
    cP
    wne
    #
    @7
    cP
    wne
    #
    wa
    #
    wa
    @0
    @4
    @24
    @25
    @5
    @11
    @0
    @4
    @5
    @26
    simpl1
    @0
    @4
    @5
    @26
    simpl2
    @6
    @24
    @25
    simprl
    @6
    @24
    @25
    simprr
    @0
    @4
    @5
    @26
    simpl3
    cA
    cP
    cR
    cT
    cF
    cG
    cH
    cK
    c.le
    cW
    cdlemg44.h
    cdlemg44.t
    cdlemg44.r
    cdlemg44.l
    cdlemg44.a
    cdlemg44a
    syl113anc
    pm2.61da2ne
end
