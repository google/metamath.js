include "co.mm"
include "cpr.mm"
include "cfv.mm"
include "lspprabs.mm"
include "neleqtrrd.mm"

theorem lspindp4
  let wph: wff ph
  let c.pl: class .+
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume lspindp3.v: |- V = ( Base ` W )
  assume lspindp3.p: |- .+ = ( +g ` W )
  assume lspindp4.n: |- N = ( LSpan ` W )
  assume lspindp4.w: |- ( ph -> W e. LMod )
  assume lspindp4.x: |- ( ph -> X e. V )
  assume lspindp4.y: |- ( ph -> Y e. V )
  assume lspindp4.z: |- ( ph -> Z e. V )
  assume lspindp4.e: |- ( ph -> -. Z e. ( N ` { X , Y } ) )


  assert |- ( ph -> -. Z e. ( N ` { X , ( X .+ Y ) } ) )

  proof
    wph
    cX
    cX
    cY
    c.pl
    co
    cpr
    cN
    cfv
    cX
    cY
    cpr
    cN
    cfv
    cZ
    lspindp4.e
    wph
    c.pl
    cN
    cV
    cW
    cX
    cY
    lspindp3.v
    lspindp3.p
    lspindp4.n
    lspindp4.w
    lspindp4.x
    lspindp4.y
    lspprabs
    neleqtrrd
end
