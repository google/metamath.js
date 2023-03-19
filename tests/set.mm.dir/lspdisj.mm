include "csn.mm"
include "cfv.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
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
include "biimpa.mm"
include "adantrr.mm"
include "wi.mm"
include "c0g.mm"
include "simprr.mm"
include "wn.mm"
include "ad2antrr.mm"
include "wo.mm"
include "simplr.mm"
include "eqeltrrd.mm"
include "simprl.mm"
include "lssvs0or.mm"
include "mpbid.mm"
include "orcomd.mm"
include "ord.mm"
include "mpd.mm"
include "oveq1d.mm"
include "lmod0vs.mm"
include "3eqtrd.mm"
include "exp32.mm"
include "adantrl.mm"
include "rexlimdv.mm"
include "ex.mm"
include "elin.mm"
include "velsn.mm"
include "3imtr4g.mm"
include "ssrdv.mm"
include "wss.mm"
include "lspsncl.mm"
include "lss0ss.mm"
include "ssind.mm"
include "eqssd.mm"

theorem lspdisj
  let wph: wff ph
  let cS: class S
  let cU: class U
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vk: setvar k
  let vv: setvar v
  assume lspdisj.v: |- V = ( Base ` W )
  assume lspdisj.o: |- .0. = ( 0g ` W )
  assume lspdisj.n: |- N = ( LSpan ` W )
  assume lspdisj.s: |- S = ( LSubSp ` W )
  assume lspdisj.w: |- ( ph -> W e. LVec )
  assume lspdisj.u: |- ( ph -> U e. S )
  assume lspdisj.x: |- ( ph -> X e. V )
  assume lspdisj.e: |- ( ph -> -. X e. U )


  assert |- ( ph -> ( ( N ` { X } ) i^i U ) = { .0. } )

  proof
    wph
    cX
    csn
    cN
    cfv
    #
    cU
    cin
    #
    c.0
    csn
    #
    wph
    vv
    @1
    @2
    wph
    vv
    cv
    #
    @0
    wcel
    #
    @3
    cU
    wcel
    #
    wa
    #
    @3
    c.0
    wceq
    #
    @3
    @1
    wcel
    @3
    @2
    wcel
    wph
    @6
    @7
    wph
    @6
    wa
    #
    @3
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
    @7
    wph
    @4
    @15
    @5
    wph
    @4
    @15
    wph
    cW
    clmod
    wcel
    #
    cX
    cV
    wcel
    #
    @4
    @15
    wb
    wph
    cW
    clvec
    wcel
    #
    @16
    lspdisj.w
    cW
    lveclmod
    syl
    #
    lspdisj.x
    @10
    @3
    vk
    @13
    @14
    cN
    cV
    cW
    cX
    @13
    eqid
    #
    @14
    eqid
    #
    lspdisj.v
    @10
    eqid
    #
    lspdisj.n
    lspsnel
    syl2anc
    biimpa
    adantrr
    @8
    @12
    @7
    vk
    @14
    wph
    @5
    @9
    @14
    wcel
    #
    @12
    @7
    wi
    wi
    @4
    wph
    @5
    wa
    #
    @23
    @12
    @7
    @24
    @23
    @12
    wa
    #
    wa
    #
    @3
    @11
    @13
    c0g
    cfv
    #
    cX
    @10
    co
    #
    c.0
    @24
    @23
    @12
    simprr
    #
    @26
    @9
    @27
    cX
    @10
    @26
    cX
    cU
    wcel
    #
    wn
    #
    @9
    @27
    wceq
    #
    wph
    @31
    @5
    @25
    lspdisj.e
    ad2antrr
    @26
    @30
    @32
    @26
    @32
    @30
    @26
    @11
    cU
    wcel
    @32
    @30
    wo
    @26
    @3
    @11
    cU
    @29
    wph
    @5
    @25
    simplr
    eqeltrrd
    @26
    @9
    cS
    @10
    cU
    @13
    @14
    cV
    cW
    cX
    @27
    lspdisj.v
    @22
    @20
    @21
    @27
    eqid
    #
    lspdisj.s
    wph
    @18
    @5
    @25
    lspdisj.w
    ad2antrr
    wph
    cU
    cS
    wcel
    #
    @5
    @25
    lspdisj.u
    ad2antrr
    wph
    @17
    @5
    @25
    lspdisj.x
    ad2antrr
    #
    @24
    @23
    @12
    simprl
    lssvs0or
    mpbid
    orcomd
    ord
    mpd
    oveq1d
    @26
    @16
    @17
    @28
    c.0
    wceq
    wph
    @16
    @5
    @25
    @19
    ad2antrr
    @35
    @10
    @13
    @27
    cV
    cW
    cX
    c.0
    lspdisj.v
    @20
    @22
    @33
    lspdisj.o
    lmod0vs
    syl2anc
    3eqtrd
    exp32
    adantrl
    rexlimdv
    mpd
    ex
    @3
    @0
    cU
    elin
    vv
    c.0
    velsn
    3imtr4g
    ssrdv
    wph
    @2
    @0
    cU
    wph
    @16
    @0
    cS
    wcel
    #
    @2
    @0
    wss
    @19
    wph
    @16
    @17
    @36
    @19
    lspdisj.x
    cS
    cN
    cV
    cW
    cX
    lspdisj.v
    lspdisj.s
    lspdisj.n
    lspsncl
    syl2anc
    cS
    cW
    @0
    c.0
    lspdisj.o
    lspdisj.s
    lss0ss
    syl2anc
    wph
    @16
    @34
    @2
    cU
    wss
    @19
    lspdisj.u
    cS
    cW
    cU
    c.0
    lspdisj.o
    lspdisj.s
    lss0ss
    syl2anc
    ssind
    eqssd
end
