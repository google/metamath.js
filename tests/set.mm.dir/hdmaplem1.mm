include "csn.mm"
include "cfv.mm"
include "cun.mm"
include "wcel.mm"
include "elun1.mm"
include "nsyl.mm"
include "lspsnne2.mm"

theorem hdmaplem1
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
  assume hdmaplem1.x: |- ( ph -> X e. V )


  assert |- ( ph -> ( N ` { Z } ) =/= ( N ` { X } ) )

  proof
    wph
    cN
    cV
    cW
    cZ
    cX
    hdmaplem1.v
    hdmaplem1.n
    hdmaplem1.w
    hdmaplem1.z
    hdmaplem1.x
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
    @0
    wcel
    hdmaplem1.j
    cZ
    @0
    @1
    elun1
    nsyl
    lspsnne2
end
