include "csn.mm"
include "cfv.mm"
include "wne.mm"
include "cpr.mm"
include "wcel.mm"
include "wn.mm"
include "lspindp1.mm"
include "simpld.mm"
include "necomd.mm"
include "simprd.mm"
include "prcom.mm"
include "fveq2i.mm"
include "eleq2i.mm"
include "sylnib.mm"
include "jca.mm"

theorem lspindp2l
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
  assume lspindp1.y: |- ( ph -> X e. ( V \ { .0. } ) )
  assume lspindp1.z: |- ( ph -> Y e. V )
  assume lspindp1.x: |- ( ph -> Z e. V )
  assume lspindp1.q: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )
  assume lspindp1.e: |- ( ph -> -. Z e. ( N ` { X , Y } ) )


  assert |- ( ph -> ( ( N ` { Y } ) =/= ( N ` { Z } ) /\ -. X e. ( N ` { Y , Z } ) ) )

  proof
    wph
    cY
    csn
    cN
    cfv
    #
    cZ
    csn
    cN
    cfv
    #
    wne
    cX
    cY
    cZ
    cpr
    #
    cN
    cfv
    #
    wcel
    #
    wn
    wph
    @1
    @0
    wph
    @1
    @0
    wne
    #
    cX
    cZ
    cY
    cpr
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    wph
    cN
    cV
    cW
    cX
    cY
    c.0
    cZ
    lspindp1.v
    lspindp1.o
    lspindp1.n
    lspindp1.w
    lspindp1.y
    lspindp1.z
    lspindp1.x
    lspindp1.q
    lspindp1.e
    lspindp1
    #
    simpld
    necomd
    wph
    @8
    @4
    wph
    @5
    @9
    @10
    simprd
    @7
    @3
    cX
    @6
    @2
    cN
    cZ
    cY
    prcom
    fveq2i
    eleq2i
    sylnib
    jca
end
