include "cpr.mm"
include "cfv.mm"
include "lspprid1.mm"
include "prcom.mm"
include "fveq2i.mm"
include "syl6eleq.mm"

theorem lspprid2
  let wph: wff ph
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lspprid.v: |- V = ( Base ` W )
  assume lspprid.n: |- N = ( LSpan ` W )
  assume lspprid.w: |- ( ph -> W e. LMod )
  assume lspprid.x: |- ( ph -> X e. V )
  assume lspprid.y: |- ( ph -> Y e. V )


  assert |- ( ph -> Y e. ( N ` { X , Y } ) )

  proof
    wph
    cY
    cY
    cX
    cpr
    #
    cN
    cfv
    cX
    cY
    cpr
    #
    cN
    cfv
    wph
    cN
    cV
    cW
    cY
    cX
    lspprid.v
    lspprid.n
    lspprid.w
    lspprid.y
    lspprid.x
    lspprid1
    @0
    @1
    cN
    cY
    cX
    prcom
    fveq2i
    syl6eleq
end
