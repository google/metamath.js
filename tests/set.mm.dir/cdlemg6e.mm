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
include "wrex.mm"
include "simp1.mm"
include "simp21.mm"
include "simp31.mm"
include "ltrnel.mm"
include "syl3anc.mm"
include "cdlemb3.mm"
include "cdlemg6d.mm"
include "exp4c.mm"
include "imp4a.mm"
include "rexlimdv.mm"
include "mpd.mm"

theorem cdlemg6e
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ F e. T ) /\ ( G e. T /\ Q .<_ ( P .\/ V ) /\ ( F ` ( G ` P ) ) = P ) ) -> ( F ` ( G ` Q ) ) = Q )

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
    cW
    c.le
    wbr
    wn
    #
    @11
    cP
    @7
    c.or
    co
    c.le
    wbr
    wn
    #
    wa
    #
    vr
    cA
    wrex
    #
    cQ
    cG
    cfv
    cF
    cfv
    cQ
    wceq
    #
    @10
    @0
    @1
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
    @15
    @0
    @4
    @9
    simp1
    #
    @0
    @1
    @2
    @3
    @9
    simp21
    #
    @10
    @0
    @5
    @1
    @17
    @18
    @0
    @4
    @5
    @6
    @8
    simp31
    @19
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
    cA
    cP
    @7
    cH
    c.or
    cK
    c.le
    cW
    vr
    cdlemg4.l
    cdlemg4.j
    cdlemg4.a
    cdlemg4.h
    cdlemb3
    syl3anc
    @10
    @14
    @16
    vr
    cA
    @10
    @11
    cA
    wcel
    #
    @12
    @13
    @16
    @10
    @20
    @12
    @13
    @16
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
    cdlemg6d
    exp4c
    imp4a
    rexlimdv
    mpd
end
