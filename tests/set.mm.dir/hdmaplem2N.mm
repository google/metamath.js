include "csn.mm"
include "cfv.mm"
include "cun.mm"
include "wcel.mm"
include "elun2.mm"
include "nsyl.mm"
include "lspsnne2.mm"

theorem hdmaplem2N
  let wph: wff ph
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume hdmaplem1.v: |- V = ( Base ` W )
  assume hdmaplem1.n: |- N = ( LSpan ` W )
  assume hdmaplem1.w: |- ( ph -> W e. LMod )
  assume hdmaplem1.z: |- ( ph -> Z e. V )
  assume hdmaplem1.j: |- ( ph -> -. Z e. ( ( N ` { X } ) u. ( N ` { Y } ) ) )
  assume hdmaplem1.y: |- ( ph -> Y e. V )


  assert |- ( ph -> ( N ` { Z } ) =/= ( N ` { Y } ) )

  proof
    wph
    cN
    cV
    cW
    cZ
    cY
    hdmaplem1.v
    hdmaplem1.n
    hdmaplem1.w
    hdmaplem1.z
    hdmaplem1.y
    wph
    cZ
    cX
    csn
    cN
    cfv
    #
    cY
    csn
    cN
    cfv
    #
    cun
    wcel
    cZ
    @1
    wcel
    hdmaplem1.j
    cZ
    @1
    @0
    elun2
    nsyl
    lspsnne2
end
