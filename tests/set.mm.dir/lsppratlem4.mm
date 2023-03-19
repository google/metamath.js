include "cv.mm"
include "cpr.mm"
include "cfv.mm"
include "wcel.mm"
include "clmod.mm"
include "wss.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "csn.mm"
include "cdif.mm"
include "lssss.mm"
include "ssdifssd.mm"
include "sseldd.mm"
include "lspprcl.mm"
include "cun.mm"
include "df-pr.mm"
include "snsspr1.mm"
include "prssi.mm"
include "syl2anc.mm"
include "lspssid.mm"
include "syl5ss.mm"
include "snssd.mm"
include "pssssd.mm"
include "snsspr2.mm"
include "unssd.mm"
include "syl5eqss.mm"
include "lspssp.mm"
include "syl3anc.mm"
include "sstrd.mm"
include "fveq2i.mm"
include "syl6sseq.mm"
include "ssdifd.mm"
include "lspsolv.mm"
include "syl13anc.mm"
include "syl6eleqr.mm"
include "jca.mm"

theorem lsppratlem4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cU: class U
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume lspprat.v: |- V = ( Base ` W )
  assume lspprat.s: |- S = ( LSubSp ` W )
  assume lspprat.n: |- N = ( LSpan ` W )
  assume lspprat.w: |- ( ph -> W e. LVec )
  assume lspprat.u: |- ( ph -> U e. S )
  assume lspprat.x: |- ( ph -> X e. V )
  assume lspprat.y: |- ( ph -> Y e. V )
  assume lspprat.p: |- ( ph -> U C. ( N ` { X , Y } ) )
  assume lsppratlem1.o: |- .0. = ( 0g ` W )
  assume lsppratlem1.x2: |- ( ph -> x e. ( U \ { .0. } ) )
  assume lsppratlem1.y2: |- ( ph -> y e. ( U \ ( N ` { x } ) ) )
  assume lsppratlem4.x3: |- ( ph -> X e. ( N ` { x , Y } ) )


  assert |- ( ph -> ( X e. ( N ` { x , y } ) /\ Y e. ( N ` { x , y } ) ) )

  proof
    wph
    cX
    vx
    cv
    #
    vy
    cv
    #
    cpr
    #
    cN
    cfv
    #
    wcel
    cY
    @3
    wcel
    wph
    @0
    cY
    cpr
    #
    cN
    cfv
    #
    @3
    cX
    wph
    cW
    clmod
    wcel
    #
    @3
    cS
    wcel
    @4
    @3
    wss
    @5
    @3
    wss
    wph
    cW
    clvec
    wcel
    #
    @6
    lspprat.w
    cW
    lveclmod
    syl
    #
    wph
    cS
    cN
    cV
    cW
    @0
    @1
    lspprat.v
    lspprat.s
    lspprat.n
    @8
    wph
    cU
    c.0
    csn
    #
    cdif
    cV
    @0
    wph
    cU
    cV
    @9
    wph
    cU
    cS
    wcel
    cU
    cV
    wss
    lspprat.u
    cS
    cU
    cV
    cW
    lspprat.v
    lspprat.s
    lssss
    syl
    #
    ssdifssd
    lsppratlem1.x2
    sseldd
    #
    wph
    cU
    @0
    csn
    #
    cN
    cfv
    #
    cdif
    #
    cV
    @1
    wph
    cU
    cV
    @13
    @10
    ssdifssd
    lsppratlem1.y2
    sseldd
    #
    lspprcl
    wph
    @4
    @12
    cY
    csn
    #
    cun
    #
    @3
    @0
    cY
    df-pr
    #
    wph
    @12
    @16
    @3
    wph
    @12
    @2
    @3
    @0
    @1
    snsspr1
    wph
    @6
    @2
    cV
    wss
    #
    @2
    @3
    wss
    @8
    wph
    @0
    cV
    wcel
    #
    @1
    cV
    wcel
    @19
    @11
    @15
    @0
    @1
    cV
    prssi
    syl2anc
    @2
    cN
    cV
    cW
    lspprat.v
    lspprat.n
    lspssid
    syl2anc
    syl5ss
    wph
    cY
    @3
    wph
    cY
    @12
    @1
    csn
    cun
    #
    cN
    cfv
    #
    @3
    wph
    @7
    @12
    cV
    wss
    cY
    cV
    wcel
    #
    @1
    @17
    cN
    cfv
    #
    @13
    cdif
    #
    wcel
    cY
    @22
    wcel
    lspprat.w
    wph
    @0
    cV
    @11
    snssd
    lspprat.y
    wph
    @14
    @25
    @1
    wph
    cU
    @24
    @13
    wph
    cU
    @5
    @24
    wph
    cU
    cX
    cY
    cpr
    #
    cN
    cfv
    #
    @5
    wph
    cU
    @27
    lspprat.p
    pssssd
    wph
    @6
    @5
    cS
    wcel
    @26
    @5
    wss
    @27
    @5
    wss
    @8
    wph
    cS
    cN
    cV
    cW
    @0
    cY
    lspprat.v
    lspprat.s
    lspprat.n
    @8
    @11
    lspprat.y
    lspprcl
    wph
    @26
    cX
    csn
    #
    @16
    cun
    @5
    cX
    cY
    df-pr
    wph
    @28
    @16
    @5
    wph
    cX
    @5
    lsppratlem4.x3
    snssd
    wph
    @16
    @4
    @5
    @0
    cY
    snsspr2
    wph
    @6
    @4
    cV
    wss
    #
    @4
    @5
    wss
    @8
    wph
    @20
    @23
    @29
    @11
    lspprat.y
    @0
    cY
    cV
    prssi
    syl2anc
    @4
    cN
    cV
    cW
    lspprat.v
    lspprat.n
    lspssid
    syl2anc
    syl5ss
    unssd
    syl5eqss
    cS
    @26
    @5
    cN
    cW
    lspprat.s
    lspprat.n
    lspssp
    syl3anc
    sstrd
    @4
    @17
    cN
    @18
    fveq2i
    syl6sseq
    ssdifd
    lsppratlem1.y2
    sseldd
    @12
    cS
    cN
    cV
    cW
    @1
    cY
    lspprat.v
    lspprat.s
    lspprat.n
    lspsolv
    syl13anc
    @2
    @21
    cN
    @0
    @1
    df-pr
    fveq2i
    syl6eleqr
    #
    snssd
    unssd
    syl5eqss
    cS
    @4
    @3
    cN
    cW
    lspprat.s
    lspprat.n
    lspssp
    syl3anc
    lsppratlem4.x3
    sseldd
    @30
    jca
end
