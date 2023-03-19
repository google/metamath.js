include "csn.mm"
include "cfv.mm"
include "necomd.mm"
include "cpr.mm"
include "wcel.mm"
include "prcom.mm"
include "fveq2i.mm"
include "eleq2i.mm"
include "sylnib.mm"
include "lspindp1.mm"

theorem lspindp2
  let wph: wff ph
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  assume lspindp1.v: |- V = ( Base ` W )
  assume lspindp1.o: |- .0. = ( 0g ` W )
  assume lspindp1.n: |- N = ( LSpan ` W )
  assume lspindp1.w: |- ( ph -> W e. LVec )
  assume lspindp2.x: |- ( ph -> X e. V )
  assume lspindp2.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume lspindp2.z: |- ( ph -> Z e. V )
  assume lspindp2.q: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )
  assume lspindp2.e: |- ( ph -> -. Z e. ( N ` { X , Y } ) )


  assert |- ( ph -> ( ( N ` { Z } ) =/= ( N ` { X } ) /\ -. Y e. ( N ` { Z , X } ) ) )

  proof
    wph
    cN
    cV
    cW
    cY
    cX
    c.0
    cZ
    lspindp1.v
    lspindp1.o
    lspindp1.n
    lspindp1.w
    lspindp2.y
    lspindp2.x
    lspindp2.z
    wph
    cX
    csn
    cN
    cfv
    cY
    csn
    cN
    cfv
    lspindp2.q
    necomd
    wph
    cZ
    cX
    cY
    cpr
    #
    cN
    cfv
    #
    wcel
    cZ
    cY
    cX
    cpr
    #
    cN
    cfv
    #
    wcel
    lspindp2.e
    @1
    @3
    cZ
    @0
    @2
    cN
    cX
    cY
    prcom
    fveq2i
    eleq2i
    sylnib
    lspindp1
end
