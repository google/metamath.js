include "csn.mm"
include "cfv.mm"
include "cin.mm"
include "wceq.mm"
include "wa.mm"
include "sneq.mm"
include "fveq2d.mm"
include "clmod.mm"
include "wcel.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "lspsn0.mm"
include "sylan9eqr.mm"
include "ineq1d.mm"
include "wss.mm"
include "clss.mm"
include "eqid.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "lss0ss.mm"
include "df-ss.mm"
include "sylib.mm"
include "adantr.mm"
include "eqtrd.mm"
include "wne.mm"
include "wn.mm"
include "simpr.mm"
include "simplr.mm"
include "lspsneleq.mm"
include "ex.mm"
include "necon3ad.mm"
include "mpd.mm"
include "lspdisj.mm"
include "pm2.61dane.mm"

theorem lspdisj2
  let wph: wff ph
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume lspdisj2.v: |- V = ( Base ` W )
  assume lspdisj2.o: |- .0. = ( 0g ` W )
  assume lspdisj2.n: |- N = ( LSpan ` W )
  assume lspdisj2.w: |- ( ph -> W e. LVec )
  assume lspdisj2.x: |- ( ph -> X e. V )
  assume lspdisj2.y: |- ( ph -> Y e. V )
  assume lspdisj2.q: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )


  assert |- ( ph -> ( ( N ` { X } ) i^i ( N ` { Y } ) ) = { .0. } )

  proof
    wph
    cX
    csn
    #
    cN
    cfv
    #
    cY
    csn
    cN
    cfv
    #
    cin
    #
    c.0
    csn
    #
    wceq
    cX
    c.0
    wph
    cX
    c.0
    wceq
    #
    wa
    #
    @3
    @4
    @2
    cin
    #
    @4
    @6
    @1
    @4
    @2
    @5
    wph
    @1
    @4
    cN
    cfv
    #
    @4
    @5
    @0
    @4
    cN
    cX
    c.0
    sneq
    fveq2d
    wph
    cW
    clmod
    wcel
    #
    @8
    @4
    wceq
    wph
    cW
    clvec
    wcel
    #
    @9
    lspdisj2.w
    cW
    lveclmod
    syl
    #
    cN
    cW
    c.0
    lspdisj2.o
    lspdisj2.n
    lspsn0
    syl
    sylan9eqr
    ineq1d
    wph
    @7
    @4
    wceq
    #
    @5
    wph
    @4
    @2
    wss
    #
    @12
    wph
    @9
    @2
    cW
    clss
    cfv
    #
    wcel
    #
    @13
    @11
    wph
    @9
    cY
    cV
    wcel
    #
    @15
    @11
    lspdisj2.y
    @14
    cN
    cV
    cW
    cY
    lspdisj2.v
    @14
    eqid
    #
    lspdisj2.n
    lspsncl
    syl2anc
    #
    @14
    cW
    @2
    c.0
    lspdisj2.o
    @17
    lss0ss
    syl2anc
    @4
    @2
    df-ss
    sylib
    adantr
    eqtrd
    wph
    cX
    c.0
    wne
    #
    wa
    #
    @14
    @2
    cN
    cV
    cW
    cX
    c.0
    lspdisj2.v
    lspdisj2.o
    lspdisj2.n
    @17
    wph
    @10
    @19
    lspdisj2.w
    adantr
    #
    wph
    @15
    @19
    @18
    adantr
    wph
    cX
    cV
    wcel
    @19
    lspdisj2.x
    adantr
    @20
    @1
    @2
    wne
    #
    cX
    @2
    wcel
    #
    wn
    wph
    @22
    @19
    lspdisj2.q
    adantr
    @20
    @23
    @1
    @2
    @20
    @23
    @1
    @2
    wceq
    @20
    @23
    wa
    cN
    cV
    cW
    cY
    cX
    c.0
    lspdisj2.v
    lspdisj2.o
    lspdisj2.n
    @20
    @10
    @23
    @21
    adantr
    @20
    @16
    @23
    wph
    @16
    @19
    lspdisj2.y
    adantr
    adantr
    @20
    @23
    simpr
    wph
    @19
    @23
    simplr
    lspsneleq
    ex
    necon3ad
    mpd
    lspdisj
    pm2.61dane
end
