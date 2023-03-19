include "co.mm"
include "wcel.mm"
include "w3o.mm"
include "3mix3d.mm"
include "tgellng.mm"
include "mpbird.mm"

theorem btwnlng3
  let wph: wff ph
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume btwnlng1.p: |- P = ( Base ` G )
  assume btwnlng1.i: |- I = ( Itv ` G )
  assume btwnlng1.l: |- L = ( LineG ` G )
  assume btwnlng1.g: |- ( ph -> G e. TarskiG )
  assume btwnlng1.x: |- ( ph -> X e. P )
  assume btwnlng1.y: |- ( ph -> Y e. P )
  assume btwnlng1.z: |- ( ph -> Z e. P )
  assume btwnlng1.d: |- ( ph -> X =/= Y )
  assume btwnlng3.1: |- ( ph -> Y e. ( X I Z ) )


  assert |- ( ph -> Z e. ( X L Y ) )

  proof
    wph
    cZ
    cX
    cY
    cL
    co
    wcel
    cZ
    cX
    cY
    cI
    co
    wcel
    #
    cX
    cZ
    cY
    cI
    co
    wcel
    #
    cY
    cX
    cZ
    cI
    co
    wcel
    #
    w3o
    wph
    @2
    @0
    @1
    btwnlng3.1
    3mix3d
    wph
    cP
    cG
    cI
    cL
    cX
    cY
    cZ
    btwnlng1.p
    btwnlng1.l
    btwnlng1.i
    btwnlng1.g
    btwnlng1.x
    btwnlng1.y
    btwnlng1.d
    btwnlng1.z
    tgellng
    mpbird
end
