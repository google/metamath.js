include "cpr.mm"
include "cfv.mm"
include "wcel.mm"
include "prcom.mm"
include "fveq2i.mm"
include "eleq2i.mm"
include "sylnib.mm"
include "lspexchn1.mm"

theorem lspexchn2
  let wph: wff ph
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume lspexchn2.v: |- V = ( Base ` W )
  assume lspexchn2.n: |- N = ( LSpan ` W )
  assume lspexchn2.w: |- ( ph -> W e. LVec )
  assume lspexchn2.x: |- ( ph -> X e. V )
  assume lspexchn2.y: |- ( ph -> Y e. V )
  assume lspexchn2.z: |- ( ph -> Z e. V )
  assume lspexchn2.q: |- ( ph -> -. Y e. ( N ` { Z } ) )
  assume lspexchn2.e: |- ( ph -> -. X e. ( N ` { Z , Y } ) )


  assert |- ( ph -> -. Y e. ( N ` { Z , X } ) )

  proof
    wph
    cY
    cX
    cZ
    cpr
    #
    cN
    cfv
    #
    wcel
    cY
    cZ
    cX
    cpr
    #
    cN
    cfv
    #
    wcel
    wph
    cN
    cV
    cW
    cX
    cY
    cZ
    lspexchn2.v
    lspexchn2.n
    lspexchn2.w
    lspexchn2.x
    lspexchn2.y
    lspexchn2.z
    lspexchn2.q
    wph
    cX
    cZ
    cY
    cpr
    #
    cN
    cfv
    #
    wcel
    cX
    cY
    cZ
    cpr
    #
    cN
    cfv
    #
    wcel
    lspexchn2.e
    @5
    @7
    cX
    @4
    @6
    cN
    cZ
    cY
    prcom
    fveq2i
    eleq2i
    sylnib
    lspexchn1
    @1
    @3
    cY
    @0
    @2
    cN
    cX
    cZ
    prcom
    fveq2i
    eleq2i
    sylnib
end
