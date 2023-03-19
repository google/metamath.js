include "csn.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "csca.mm"
include "cbs.mm"
include "wrex.mm"
include "clmod.mm"
include "wb.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "eqid.mm"
include "lspsnel.mm"
include "syl2anc.mm"
include "wa.mm"
include "simpr.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "c0g.mm"
include "wne.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "oveq1d.mm"
include "lmod0vs.mm"
include "ad3antrrr.mm"
include "3eqtrd.mm"
include "ex.mm"
include "necon3d.mm"
include "mpd.mm"
include "lspsnvs.mm"
include "syl121anc.mm"
include "eqtrd.mm"
include "rexlimdva.mm"
include "sylbid.mm"

theorem lspsneleq
  let wph: wff ph
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vk: setvar k
  assume lspsneleq.v: |- V = ( Base ` W )
  assume lspsneleq.o: |- .0. = ( 0g ` W )
  assume lspsneleq.n: |- N = ( LSpan ` W )
  assume lspsneleq.w: |- ( ph -> W e. LVec )
  assume lspsneleq.x: |- ( ph -> X e. V )
  assume lspsneleq.y: |- ( ph -> Y e. ( N ` { X } ) )
  assume lspsneleq.z: |- ( ph -> Y =/= .0. )


  assert |- ( ph -> ( N ` { Y } ) = ( N ` { X } ) )

  proof
    wph
    cY
    cX
    csn
    cN
    cfv
    #
    wcel
    #
    cY
    csn
    #
    cN
    cfv
    #
    @0
    wceq
    #
    lspsneleq.y
    wph
    @1
    cY
    vk
    cv
    #
    cX
    cW
    cvsca
    cfv
    #
    co
    #
    wceq
    #
    vk
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    wrex
    #
    @4
    wph
    cW
    clmod
    wcel
    #
    cX
    cV
    wcel
    #
    @1
    @11
    wb
    wph
    cW
    clvec
    wcel
    #
    @12
    lspsneleq.w
    cW
    lveclmod
    syl
    #
    lspsneleq.x
    @6
    cY
    vk
    @9
    @10
    cN
    cV
    cW
    cX
    @9
    eqid
    #
    @10
    eqid
    #
    lspsneleq.v
    @6
    eqid
    #
    lspsneleq.n
    lspsnel
    syl2anc
    wph
    @8
    @4
    vk
    @10
    wph
    @5
    @10
    wcel
    #
    wa
    #
    @8
    @4
    @20
    @8
    wa
    #
    @3
    @7
    csn
    #
    cN
    cfv
    #
    @0
    @21
    @2
    @22
    cN
    @21
    cY
    @7
    @20
    @8
    simpr
    sneqd
    fveq2d
    @21
    @14
    @19
    @5
    @9
    c0g
    cfv
    #
    wne
    #
    @13
    @23
    @0
    wceq
    wph
    @14
    @19
    @8
    lspsneleq.w
    ad2antrr
    wph
    @19
    @8
    simplr
    @21
    cY
    c.0
    wne
    #
    @25
    wph
    @26
    @19
    @8
    lspsneleq.z
    ad2antrr
    @21
    @5
    @24
    cY
    c.0
    @21
    @5
    @24
    wceq
    #
    cY
    c.0
    wceq
    @21
    @27
    wa
    #
    cY
    @7
    @24
    cX
    @6
    co
    #
    c.0
    @20
    @8
    @27
    simplr
    @28
    @5
    @24
    cX
    @6
    @21
    @27
    simpr
    oveq1d
    wph
    @29
    c.0
    wceq
    #
    @19
    @8
    @27
    wph
    @12
    @13
    @30
    @15
    lspsneleq.x
    @6
    @9
    @24
    cV
    cW
    cX
    c.0
    lspsneleq.v
    @16
    @18
    @24
    eqid
    #
    lspsneleq.o
    lmod0vs
    syl2anc
    ad3antrrr
    3eqtrd
    ex
    necon3d
    mpd
    wph
    @13
    @19
    @8
    lspsneleq.x
    ad2antrr
    @5
    @6
    @9
    @10
    cN
    cV
    cW
    cX
    @24
    lspsneleq.v
    @16
    @18
    @17
    @31
    lspsneleq.n
    lspsnvs
    syl121anc
    eqtrd
    ex
    rexlimdva
    sylbid
    mpd
end
