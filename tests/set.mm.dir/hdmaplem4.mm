include "csn.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "cun.mm"
include "lspsnne1.mm"
include "wo.mm"
include "wa.mm"
include "ioran.mm"
include "elun.mm"
include "xchnxbir.mm"
include "sylanbrc.mm"

theorem hdmaplem4
  let wph: wff ph
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  assume hdmaplem1.v: |- V = ( Base ` W )
  assume hdmaplem1.n: |- N = ( LSpan ` W )
  assume hdmaplem4.o: |- .0. = ( 0g ` W )
  assume hdmaplem4.w: |- ( ph -> W e. LVec )
  assume hdmaplem4.x: |- ( ph -> X e. V )
  assume hdmaplem4.y: |- ( ph -> Y e. V )
  assume hdmaplem4.z: |- ( ph -> Z e. ( V \ { .0. } ) )
  assume hdmaplem4.e: |- ( ph -> ( N ` { Z } ) =/= ( N ` { X } ) )
  assume hdmaplem4.f: |- ( ph -> ( N ` { Z } ) =/= ( N ` { Y } ) )


  assert |- ( ph -> -. Z e. ( ( N ` { X } ) u. ( N ` { Y } ) ) )

  proof
    wph
    cZ
    cX
    csn
    cN
    cfv
    #
    wcel
    #
    wn
    #
    cZ
    cY
    csn
    cN
    cfv
    #
    wcel
    #
    wn
    #
    cZ
    @0
    @3
    cun
    wcel
    #
    wn
    wph
    cN
    cV
    cW
    cZ
    cX
    c.0
    hdmaplem1.v
    hdmaplem4.o
    hdmaplem1.n
    hdmaplem4.w
    hdmaplem4.z
    hdmaplem4.x
    hdmaplem4.e
    lspsnne1
    wph
    cN
    cV
    cW
    cZ
    cY
    c.0
    hdmaplem1.v
    hdmaplem4.o
    hdmaplem1.n
    hdmaplem4.w
    hdmaplem4.z
    hdmaplem4.y
    hdmaplem4.f
    lspsnne1
    @1
    @4
    wo
    @2
    @5
    wa
    @6
    @1
    @4
    ioran
    cZ
    @0
    @3
    elun
    xchnxbir
    sylanbrc
end
