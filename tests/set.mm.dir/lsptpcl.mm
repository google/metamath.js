include "clmod.mm"
include "wcel.mm"
include "ctp.mm"
include "wss.mm"
include "cfv.mm"
include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "df-tp.mm"
include "prssi.mm"
include "syl2anc.mm"
include "snssd.mm"
include "unssd.mm"
include "syl5eqss.mm"
include "lspcl.mm"

theorem lsptpcl
  let wph: wff ph
  let cS: class S
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
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
  assume lsptpcl.z: |- ( ph -> Z e. V )


  assert |- ( ph -> ( N ` { X , Y , Z } ) e. S )

  proof
    wph
    cW
    clmod
    wcel
    cX
    cY
    cZ
    ctp
    #
    cV
    wss
    @0
    cN
    cfv
    cS
    wcel
    lspprcl.w
    wph
    @0
    cX
    cY
    cpr
    #
    cZ
    csn
    #
    cun
    cV
    cX
    cY
    cZ
    df-tp
    wph
    @1
    @2
    cV
    wph
    cX
    cV
    wcel
    cY
    cV
    wcel
    @1
    cV
    wss
    lspprcl.x
    lspprcl.y
    cX
    cY
    cV
    prssi
    syl2anc
    wph
    cZ
    cV
    lsptpcl.z
    snssd
    unssd
    syl5eqss
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
