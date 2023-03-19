include "co.mm"
include "cv.mm"
include "wcel.mm"
include "w3o.mm"
include "crab.mm"
include "tglngval.mm"
include "ssrab2.mm"
include "syl6eqss.mm"

theorem tglnssp
  let wph: wff ph
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume tglngval.p: |- P = ( Base ` G )
  assume tglngval.l: |- L = ( LineG ` G )
  assume tglngval.i: |- I = ( Itv ` G )
  assume tglngval.g: |- ( ph -> G e. TarskiG )
  assume tglngval.x: |- ( ph -> X e. P )
  assume tglngval.y: |- ( ph -> Y e. P )
  assume tglngval.z: |- ( ph -> X =/= Y )


  assert |- ( ph -> ( X L Y ) C_ P )

  proof
    wph
    cX
    cY
    cL
    co
    vz
    cv
    #
    cX
    cY
    cI
    co
    wcel
    cX
    @0
    cY
    cI
    co
    wcel
    cY
    cX
    @0
    cI
    co
    wcel
    w3o
    #
    vz
    cP
    crab
    cP
    wph
    vz
    cP
    cG
    cI
    cL
    cX
    cY
    tglngval.p
    tglngval.l
    tglngval.i
    tglngval.g
    tglngval.x
    tglngval.y
    tglngval.z
    tglngval
    @1
    vz
    cP
    ssrab2
    syl6eqss
end
