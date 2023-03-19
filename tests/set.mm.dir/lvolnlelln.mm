include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "wne.mm"
include "cjn.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "catm.mm"
include "wrex.mm"
include "wbr.mm"
include "wn.mm"
include "simp3.mm"
include "wb.mm"
include "eqid.mm"
include "islln2.mm"
include "3ad2ant1.mm"
include "mpbid.mm"
include "simp11.mm"
include "simp12.mm"
include "simp2l.mm"
include "simp2r.mm"
include "lvolnle3at.mm"
include "syl23anc.mm"
include "simp3r.mm"
include "hlatjidm.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "breq2d.mm"
include "mtbird.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "adantld.mm"
include "mpd.mm"

theorem lvolnlelln
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let vp: setvar p
  let vq: setvar q
  assume lvolnlelln.l: |- .<_ = ( le ` K )
  assume lvolnlelln.n: |- N = ( LLines ` K )
  assume lvolnlelln.v: |- V = ( LVols ` K )


  assert |- ( ( K e. HL /\ X e. V /\ Y e. N ) -> -. X .<_ Y )

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
    cN
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
    vp
    cv
    #
    vq
    cv
    #
    wne
    #
    cY
    @6
    @7
    cK
    cjn
    cfv
    #
    co
    #
    wceq
    #
    wa
    #
    vq
    cK
    catm
    cfv
    #
    wrex
    vp
    @13
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
    @15
    @0
    @1
    @2
    simp3
    @0
    @1
    @2
    @15
    wb
    @2
    @13
    @4
    @9
    cK
    cN
    cY
    vq
    vp
    @4
    eqid
    @9
    eqid
    #
    @13
    eqid
    #
    lvolnlelln.n
    islln2
    3ad2ant1
    mpbid
    @3
    @14
    @17
    @5
    @3
    @12
    @17
    vp
    vq
    @13
    @13
    @3
    @6
    @13
    wcel
    #
    @7
    @13
    wcel
    #
    wa
    #
    @12
    @17
    @3
    @22
    @12
    w3a
    #
    @16
    cX
    @6
    @6
    @9
    co
    #
    @7
    @9
    co
    #
    c.le
    wbr
    #
    @23
    @0
    @1
    @20
    @20
    @21
    @26
    wn
    @0
    @1
    @2
    @22
    @12
    simp11
    #
    @0
    @1
    @2
    @22
    @12
    simp12
    @3
    @20
    @21
    @12
    simp2l
    #
    @28
    @3
    @20
    @21
    @12
    simp2r
    @13
    @6
    @6
    @7
    @9
    cK
    c.le
    cV
    cX
    lvolnlelln.l
    @18
    @19
    lvolnlelln.v
    lvolnle3at
    syl23anc
    @23
    cY
    @25
    cX
    c.le
    @23
    cY
    @10
    @25
    @3
    @22
    @8
    @11
    simp3r
    @23
    @24
    @6
    @7
    @9
    @23
    @0
    @20
    @24
    @6
    wceq
    @27
    @28
    @13
    @9
    cK
    @6
    @18
    @19
    hlatjidm
    syl2anc
    oveq1d
    eqtr4d
    breq2d
    mtbird
    3exp
    rexlimdvv
    adantld
    mpd
end
