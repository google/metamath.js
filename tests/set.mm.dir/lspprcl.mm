include "clmod.mm"
include "wcel.mm"
include "cpr.mm"
include "wss.mm"
include "cfv.mm"
include "prssi.mm"
include "syl2anc.mm"
include "lspcl.mm"

theorem lspprcl
  let wph: wff ph
  let cS: class S
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vp: setvar p
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let cU: class U
  assume lspval.v: |- V = ( Base ` W )
  assume lspval.s: |- S = ( LSubSp ` W )
  assume lspval.n: |- N = ( LSpan ` W )
  assume lspprcl.w: |- ( ph -> W e. LMod )
  assume lspprcl.x: |- ( ph -> X e. V )
  assume lspprcl.y: |- ( ph -> Y e. V )


  assert |- ( ph -> ( N ` { X , Y } ) e. S )

  proof
    wph
    cW
    clmod
    wcel
    cX
    cY
    cpr
    #
    cV
    wss
    #
    @0
    cN
    cfv
    cS
    wcel
    lspprcl.w
    wph
    cX
    cV
    wcel
    cY
    cV
    wcel
    @1
    lspprcl.x
    lspprcl.y
    cX
    cY
    cV
    prssi
    syl2anc
    cS
    @0
    cN
    cV
    cW
    lspval.v
    lspval.s
    lspval.n
    lspcl
    syl2anc
end
