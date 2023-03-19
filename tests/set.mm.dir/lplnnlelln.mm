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
include "lplnnle2at.mm"
include "syl13anc.mm"
include "simp3r.mm"
include "breq2d.mm"
include "mtbird.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "adantld.mm"
include "mpd.mm"

theorem lplnnlelln
  let cP: class P
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let cX: class X
  let cY: class Y
  let vq: setvar q
  let vr: setvar r
  assume lplnnlelln.l: |- .<_ = ( le ` K )
  assume lplnnlelln.n: |- N = ( LLines ` K )
  assume lplnnlelln.p: |- P = ( LPlanes ` K )


  assert |- ( ( K e. HL /\ X e. P /\ Y e. N ) -> -. X .<_ Y )

  proof
    cK
    chlt
    wcel
    #
    cX
    cP
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
    vq
    cv
    #
    vr
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
    vr
    cK
    catm
    cfv
    #
    wrex
    vq
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
    vr
    vq
    @4
    eqid
    @9
    eqid
    #
    @13
    eqid
    #
    lplnnlelln.n
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
    vq
    vr
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
    @10
    c.le
    wbr
    #
    @23
    @0
    @1
    @20
    @21
    @24
    wn
    @0
    @1
    @2
    @22
    @12
    simp11
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
    @3
    @20
    @21
    @12
    simp2r
    @13
    cP
    @6
    @7
    @9
    cK
    c.le
    cX
    lplnnlelln.l
    @18
    @19
    lplnnlelln.p
    lplnnle2at
    syl13anc
    @23
    cY
    @10
    cX
    c.le
    @3
    @22
    @8
    @11
    simp3r
    breq2d
    mtbird
    3exp
    rexlimdvv
    adantld
    mpd
end
