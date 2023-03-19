include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "wne.mm"
include "cjn.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "catm.mm"
include "wrex.mm"
include "wa.mm"
include "simp3.mm"
include "wb.mm"
include "eqid.mm"
include "islpln2.mm"
include "3ad2ant1.mm"
include "mpbid.mm"
include "simp1l1.mm"
include "simp1l2.mm"
include "simp1r.mm"
include "simp2l.mm"
include "simp2r.mm"
include "lvolnle3at.mm"
include "syl23anc.mm"
include "simp33.mm"
include "breq2d.mm"
include "mtbird.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "rexlimdva.mm"
include "adantld.mm"
include "mpd.mm"

theorem lvolnlelpln
  let cP: class P
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cX: class X
  let cY: class Y
  let vq: setvar q
  let vr: setvar r
  let vs: setvar s
  assume lvolnlelpln.l: |- .<_ = ( le ` K )
  assume lvolnlelpln.p: |- P = ( LPlanes ` K )
  assume lvolnlelpln.v: |- V = ( LVols ` K )


  assert |- ( ( K e. HL /\ X e. V /\ Y e. P ) -> -. X .<_ Y )

  proof
    cK
    chlt
    wcel
    #
    cX
    cV
    wcel
    #
    cY
    cP
    wcel
    #
    w3a
    #
    cY
    cK
    cbs
    cfv
    #
    wcel
    #
    vq
    cv
    #
    vr
    cv
    #
    wne
    #
    vs
    cv
    #
    @6
    @7
    cK
    cjn
    cfv
    #
    co
    #
    c.le
    wbr
    wn
    #
    cY
    @11
    @9
    @10
    co
    #
    wceq
    #
    w3a
    #
    vs
    cK
    catm
    cfv
    #
    wrex
    vr
    @16
    wrex
    #
    vq
    @16
    wrex
    #
    wa
    #
    cX
    cY
    c.le
    wbr
    #
    wn
    #
    @3
    @2
    @19
    @0
    @1
    @2
    simp3
    @0
    @1
    @2
    @19
    wb
    @2
    @16
    @4
    cP
    @10
    cK
    c.le
    cY
    vs
    vr
    vq
    @4
    eqid
    lvolnlelpln.l
    @10
    eqid
    #
    @16
    eqid
    #
    lvolnlelpln.p
    islpln2
    3ad2ant1
    mpbid
    @3
    @18
    @21
    @5
    @3
    @17
    @21
    vq
    @16
    @3
    @6
    @16
    wcel
    #
    wa
    #
    @15
    @21
    vr
    vs
    @16
    @16
    @25
    @7
    @16
    wcel
    #
    @9
    @16
    wcel
    #
    wa
    #
    @15
    @21
    @25
    @28
    @15
    w3a
    #
    @20
    cX
    @13
    c.le
    wbr
    #
    @29
    @0
    @1
    @24
    @26
    @27
    @30
    wn
    @0
    @1
    @2
    @24
    @28
    @15
    simp1l1
    @0
    @1
    @2
    @24
    @28
    @15
    simp1l2
    @3
    @24
    @28
    @15
    simp1r
    @25
    @26
    @27
    @15
    simp2l
    @25
    @26
    @27
    @15
    simp2r
    @16
    @6
    @7
    @9
    @10
    cK
    c.le
    cV
    cX
    lvolnlelpln.l
    @22
    @23
    lvolnlelpln.v
    lvolnle3at
    syl23anc
    @29
    cY
    @13
    cX
    c.le
    @25
    @28
    @8
    @12
    @14
    simp33
    breq2d
    mtbird
    3exp
    rexlimdvv
    rexlimdva
    adantld
    mpd
end
