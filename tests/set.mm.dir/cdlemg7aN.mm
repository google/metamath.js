include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "cmee.mm"
include "co.mm"
include "cjn.mm"
include "wrex.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp2r.mm"
include "eqid.mm"
include "lhpmcvr2.mm"
include "syl21anc.mm"
include "simp11.mm"
include "simp2.mm"
include "simp3l.mm"
include "jca.mm"
include "simp12r.mm"
include "simp131.mm"
include "simp132.mm"
include "simp3r.mm"
include "cdlemg7fvN.mm"
include "syl123anc.mm"
include "simp12l.mm"
include "simp133.mm"
include "cdlemg6.mm"
include "oveq1d.mm"
include "3eqtrd.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem cdlemg7aN
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( X e. B /\ -. X .<_ W ) ) /\ ( F e. T /\ G e. T /\ ( F ` ( G ` P ) ) = P ) ) -> ( F ` ( G ` X ) ) = X )

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
    cX
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
    cX
    cW
    cK
    cmee
    cfv
    #
    co
    #
    cK
    cjn
    cfv
    #
    co
    #
    cX
    wceq
    #
    wa
    #
    vr
    cA
    wrex
    #
    cX
    cG
    cfv
    cF
    cfv
    #
    cX
    wceq
    #
    @10
    @0
    @1
    @4
    @19
    @0
    @1
    @5
    @9
    simp1l
    @0
    @1
    @5
    @9
    simp1r
    @2
    @3
    @4
    @9
    simp2r
    cA
    cB
    cH
    @15
    cK
    c.le
    @13
    cW
    cX
    vr
    cdlemg7.b
    cdlemg7.l
    @15
    eqid
    #
    @13
    eqid
    #
    cdlemg7.a
    cdlemg7.h
    lhpmcvr2
    syl21anc
    @10
    @18
    @21
    vr
    cA
    @10
    @11
    cA
    wcel
    #
    @18
    w3a
    #
    @20
    @11
    cG
    cfv
    cF
    cfv
    #
    @14
    @15
    co
    #
    @16
    cX
    @25
    @2
    @24
    @12
    wa
    #
    @4
    @6
    @7
    @17
    @20
    @27
    wceq
    @2
    @5
    @9
    @24
    @18
    simp11
    #
    @25
    @24
    @12
    @10
    @24
    @18
    simp2
    @10
    @24
    @12
    @17
    simp3l
    jca
    #
    @3
    @4
    @2
    @9
    @24
    @18
    simp12r
    @6
    @7
    @8
    @2
    @5
    @24
    @18
    simp131
    #
    @6
    @7
    @8
    @2
    @5
    @24
    @18
    simp132
    #
    @10
    @24
    @12
    @17
    simp3r
    #
    cA
    cB
    @11
    cT
    cF
    cG
    cH
    @15
    cK
    c.le
    @13
    cW
    cX
    cdlemg7.b
    cdlemg7.l
    @22
    @23
    cdlemg7.a
    cdlemg7.h
    cdlemg7.t
    cdlemg7fvN
    syl123anc
    @25
    @26
    @11
    @14
    @15
    @25
    @2
    @3
    @28
    @6
    @7
    @8
    @26
    @11
    wceq
    @29
    @3
    @4
    @2
    @9
    @24
    @18
    simp12l
    @30
    @31
    @32
    @6
    @7
    @8
    @2
    @5
    @24
    @18
    simp133
    cA
    cP
    @11
    cT
    cF
    cG
    cH
    cK
    c.le
    cW
    cdlemg7.l
    cdlemg7.a
    cdlemg7.h
    cdlemg7.t
    cdlemg6
    syl123anc
    oveq1d
    @33
    3eqtrd
    rexlimdv3a
    mpd
end
