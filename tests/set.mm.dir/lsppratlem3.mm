include "cv.mm"
include "cpr.mm"
include "cfv.mm"
include "wcel.mm"
include "csn.mm"
include "cun.mm"
include "clvec.mm"
include "wss.mm"
include "cdif.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "snssd.mm"
include "lspssv.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "pssssd.mm"
include "unssd.mm"
include "lspcl.mm"
include "df-pr.mm"
include "lspssid.mm"
include "unssbd.mm"
include "ssun1.mm"
include "a1i.mm"
include "lspss.mm"
include "syl3anc.mm"
include "c0.mm"
include "0ss.mm"
include "uncom.mm"
include "un0.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "syl6eleqr.mm"
include "eldifbd.mm"
include "wceq.mm"
include "lsp0.mm"
include "neleqtrrd.mm"
include "eldifd.mm"
include "lspsolv.mm"
include "syl13anc.mm"
include "syl6eleq.mm"
include "syl5eqss.mm"
include "lspssp.mm"
include "sstrd.mm"
include "ssdifd.mm"
include "lssss.mm"
include "ssdifssd.mm"
include "snsspr1.mm"
include "jca.mm"

theorem lsppratlem3
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
  assume lsppratlem3.x3: |- ( ph -> x e. ( N ` { Y } ) )


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
    cX
    @0
    csn
    #
    @1
    csn
    #
    cun
    #
    cN
    cfv
    #
    @3
    wph
    cW
    clvec
    wcel
    #
    @4
    cV
    wss
    cX
    cV
    wcel
    @1
    @4
    cX
    csn
    #
    cun
    #
    cN
    cfv
    #
    @4
    cN
    cfv
    #
    cdif
    #
    wcel
    cX
    @7
    wcel
    lspprat.w
    wph
    @0
    cV
    wph
    cY
    csn
    #
    cN
    cfv
    #
    cV
    @0
    wph
    cW
    clmod
    wcel
    #
    @14
    cV
    wss
    @15
    cV
    wss
    wph
    @8
    @16
    lspprat.w
    cW
    lveclmod
    syl
    #
    wph
    cY
    cV
    lspprat.y
    snssd
    @14
    cN
    cV
    cW
    lspprat.v
    lspprat.n
    lspssv
    syl2anc
    lsppratlem3.x3
    sseldd
    snssd
    #
    lspprat.x
    wph
    cU
    @12
    cdif
    #
    @13
    @1
    wph
    cU
    @11
    @12
    wph
    cU
    cX
    cY
    cpr
    #
    cN
    cfv
    #
    @11
    wph
    cU
    @21
    lspprat.p
    pssssd
    wph
    @16
    @11
    cS
    wcel
    #
    @20
    @11
    wss
    @21
    @11
    wss
    @17
    wph
    @16
    @10
    cV
    wss
    #
    @22
    @17
    wph
    @4
    @9
    cV
    @18
    wph
    cX
    cV
    lspprat.x
    snssd
    unssd
    #
    cS
    @10
    cN
    cV
    cW
    lspprat.v
    lspprat.s
    lspprat.n
    lspcl
    syl2anc
    wph
    @20
    @9
    @14
    cun
    @11
    cX
    cY
    df-pr
    wph
    @9
    @14
    @11
    wph
    @4
    @9
    @11
    wph
    @16
    @23
    @10
    @11
    wss
    @17
    @24
    @10
    cN
    cV
    cW
    lspprat.v
    lspprat.n
    lspssid
    syl2anc
    unssbd
    wph
    cY
    @11
    wph
    @12
    @11
    cY
    wph
    @16
    @23
    @4
    @10
    wss
    #
    @12
    @11
    wss
    @17
    @24
    @25
    wph
    @4
    @9
    ssun1
    a1i
    @4
    @10
    cN
    cV
    cW
    lspprat.v
    lspprat.n
    lspss
    syl3anc
    wph
    cY
    c0
    @4
    cun
    #
    cN
    cfv
    #
    @12
    wph
    @8
    c0
    cV
    wss
    #
    cY
    cV
    wcel
    @0
    c0
    @14
    cun
    #
    cN
    cfv
    #
    c0
    cN
    cfv
    #
    cdif
    wcel
    cY
    @27
    wcel
    lspprat.w
    @28
    wph
    cV
    0ss
    a1i
    lspprat.y
    wph
    @0
    @30
    @31
    wph
    @0
    @15
    @30
    lsppratlem3.x3
    @29
    @14
    cN
    @29
    @14
    c0
    cun
    @14
    c0
    @14
    uncom
    @14
    un0
    eqtri
    fveq2i
    syl6eleqr
    wph
    @31
    c.0
    csn
    #
    @0
    wph
    @0
    cU
    @32
    lsppratlem1.x2
    eldifbd
    wph
    @16
    @31
    @32
    wceq
    @17
    cN
    cW
    c.0
    lsppratlem1.o
    lspprat.n
    lsp0
    syl
    neleqtrrd
    eldifd
    c0
    cS
    cN
    cV
    cW
    @0
    cY
    lspprat.v
    lspprat.s
    lspprat.n
    lspsolv
    syl13anc
    @26
    @4
    cN
    @26
    @4
    c0
    cun
    @4
    c0
    @4
    uncom
    @4
    un0
    eqtri
    fveq2i
    syl6eleq
    #
    sseldd
    snssd
    unssd
    syl5eqss
    cS
    @20
    @11
    cN
    cW
    lspprat.s
    lspprat.n
    lspssp
    syl3anc
    sstrd
    ssdifd
    lsppratlem1.y2
    sseldd
    @4
    cS
    cN
    cV
    cW
    @1
    cX
    lspprat.v
    lspprat.s
    lspprat.n
    lspsolv
    syl13anc
    @2
    @6
    cN
    @0
    @1
    df-pr
    #
    fveq2i
    syl6eleqr
    wph
    @12
    @3
    cY
    wph
    @16
    @2
    cV
    wss
    @4
    @2
    wss
    #
    @12
    @3
    wss
    @17
    wph
    @2
    @6
    cV
    @34
    wph
    @4
    @5
    cV
    @18
    wph
    @1
    cV
    wph
    @19
    cV
    @1
    wph
    cU
    cV
    @12
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
    ssdifssd
    lsppratlem1.y2
    sseldd
    snssd
    unssd
    syl5eqss
    @35
    wph
    @0
    @1
    snsspr1
    a1i
    @4
    @2
    cN
    cV
    cW
    lspprat.v
    lspprat.n
    lspss
    syl3anc
    @33
    sseldd
    jca
end
