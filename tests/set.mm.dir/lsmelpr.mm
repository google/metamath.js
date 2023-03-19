include "cpr.mm"
include "cfv.mm"
include "wcel.mm"
include "csn.mm"
include "wss.mm"
include "co.mm"
include "clss.mm"
include "eqid.mm"
include "lspprcl.mm"
include "lspsnel5.mm"
include "lsmpr.mm"
include "sseq2d.mm"
include "bitrd.mm"

theorem lsmelpr
  let wph: wff ph
  let c.po: class .(+)
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume lsmelpr.v: |- V = ( Base ` W )
  assume lsmelpr.n: |- N = ( LSpan ` W )
  assume lsmelpr.p: |- .(+) = ( LSSum ` W )
  assume lsmelpr.w: |- ( ph -> W e. LMod )
  assume lsmelpr.x: |- ( ph -> X e. V )
  assume lsmelpr.y: |- ( ph -> Y e. V )
  assume lsmelpr.z: |- ( ph -> Z e. V )


  assert |- ( ph -> ( X e. ( N ` { Y , Z } ) <-> ( N ` { X } ) C_ ( ( N ` { Y } ) .(+) ( N ` { Z } ) ) ) )

  proof
    wph
    cX
    cY
    cZ
    cpr
    cN
    cfv
    #
    wcel
    cX
    csn
    cN
    cfv
    #
    @0
    wss
    @1
    cY
    csn
    cN
    cfv
    cZ
    csn
    cN
    cfv
    c.po
    co
    #
    wss
    wph
    cW
    clss
    cfv
    #
    @0
    cN
    cV
    cW
    cX
    lsmelpr.v
    @3
    eqid
    #
    lsmelpr.n
    lsmelpr.w
    wph
    @3
    cN
    cV
    cW
    cY
    cZ
    lsmelpr.v
    @4
    lsmelpr.n
    lsmelpr.w
    lsmelpr.y
    lsmelpr.z
    lspprcl
    lsmelpr.x
    lspsnel5
    wph
    @0
    @2
    @1
    wph
    c.po
    cN
    cV
    cW
    cY
    cZ
    lsmelpr.v
    lsmelpr.n
    lsmelpr.p
    lsmelpr.w
    lsmelpr.y
    lsmelpr.z
    lsmpr
    sseq2d
    bitrd
end
