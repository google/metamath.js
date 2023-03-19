include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "simpl11.mm"
include "simpl12.mm"
include "simpl13.mm"
include "jca.mm"
include "simpr.mm"
include "simpl2.mm"
include "simpl3.mm"
include "cjn.mm"
include "eqid.mm"
include "cdlemd9.mm"
include "syl311anc.mm"
include "ralrimiva.mm"
include "wb.mm"
include "ltrneq2.mm"
include "3ad2ant1.mm"
include "mpbid.mm"

theorem cdlemd
  let cA: class A
  let cP: class P
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vq: setvar q
  assume cdlemd.l: |- .<_ = ( le ` K )
  assume cdlemd.a: |- A = ( Atoms ` K )
  assume cdlemd.h: |- H = ( LHyp ` K )
  assume cdlemd.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ G e. T ) /\ ( P e. A /\ -. P .<_ W ) /\ ( F ` P ) = ( G ` P ) ) -> F = G )

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
    w3a
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
    cP
    cF
    cfv
    cP
    cG
    cfv
    wceq
    #
    w3a
    #
    vq
    cv
    #
    cF
    cfv
    @7
    cG
    cfv
    wceq
    #
    vq
    cA
    wral
    #
    cF
    cG
    wceq
    #
    @6
    @8
    vq
    cA
    @6
    @7
    cA
    wcel
    #
    wa
    #
    @0
    @1
    @2
    wa
    @11
    @4
    @5
    @8
    @0
    @1
    @2
    @4
    @5
    @11
    simpl11
    @12
    @1
    @2
    @0
    @1
    @2
    @4
    @5
    @11
    simpl12
    @0
    @1
    @2
    @4
    @5
    @11
    simpl13
    jca
    @6
    @11
    simpr
    @3
    @4
    @5
    @11
    simpl2
    @3
    @4
    @5
    @11
    simpl3
    cA
    cP
    @7
    cT
    cF
    cG
    cH
    cK
    cjn
    cfv
    #
    cK
    c.le
    cW
    cdlemd.l
    @13
    eqid
    cdlemd.a
    cdlemd.h
    cdlemd.t
    cdlemd9
    syl311anc
    ralrimiva
    @3
    @4
    @9
    @10
    wb
    @5
    cA
    cT
    cF
    cG
    cH
    cK
    cW
    vq
    cdlemd.a
    cdlemd.h
    cdlemd.t
    ltrneq2
    3ad2ant1
    mpbid
end
