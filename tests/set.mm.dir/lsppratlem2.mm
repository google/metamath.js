include "cpr.mm"
include "cfv.mm"
include "cv.mm"
include "clvec.mm"
include "wcel.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "wss.mm"
include "csn.mm"
include "eldifad.mm"
include "prssi.mm"
include "syl2anc.mm"
include "lssss.mm"
include "sstrd.mm"
include "lspcl.mm"
include "lspprss.mm"

theorem lsppratlem2
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
  assume lsppratlem2.x1: |- ( ph -> X e. ( N ` { x , y } ) )
  assume lsppratlem2.y1: |- ( ph -> Y e. ( N ` { x , y } ) )


  assert |- ( ph -> ( N ` { X , Y } ) C_ U )

  proof
    wph
    cX
    cY
    cpr
    cN
    cfv
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
    cU
    wph
    cS
    @3
    cN
    cW
    cX
    cY
    lspprat.s
    lspprat.n
    wph
    cW
    clvec
    wcel
    cW
    clmod
    wcel
    #
    lspprat.w
    cW
    lveclmod
    syl
    #
    wph
    @4
    @2
    cV
    wss
    @3
    cS
    wcel
    @5
    wph
    @2
    cU
    cV
    wph
    @0
    cU
    wcel
    @1
    cU
    wcel
    @2
    cU
    wss
    wph
    @0
    cU
    c.0
    csn
    lsppratlem1.x2
    eldifad
    #
    wph
    @1
    cU
    @0
    csn
    cN
    cfv
    lsppratlem1.y2
    eldifad
    #
    @0
    @1
    cU
    prssi
    syl2anc
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
    sstrd
    cS
    @2
    cN
    cV
    cW
    lspprat.v
    lspprat.s
    lspprat.n
    lspcl
    syl2anc
    lsppratlem2.x1
    lsppratlem2.y1
    lspprss
    wph
    cS
    cU
    cN
    cW
    @0
    @1
    lspprat.s
    lspprat.n
    @5
    lspprat.u
    @6
    @7
    lspprss
    sstrd
end
