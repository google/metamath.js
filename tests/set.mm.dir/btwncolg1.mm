include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "w3o.mm"
include "3mix1d.mm"
include "tgcolg.mm"
include "mpbird.mm"

theorem btwncolg1
  let wph: wff ph
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume tglngval.p: |- P = ( Base ` G )
  assume tglngval.l: |- L = ( LineG ` G )
  assume tglngval.i: |- I = ( Itv ` G )
  assume tglngval.g: |- ( ph -> G e. TarskiG )
  assume tglngval.x: |- ( ph -> X e. P )
  assume tglngval.y: |- ( ph -> Y e. P )
  assume tgcolg.z: |- ( ph -> Z e. P )
  assume btwncolg1.z: |- ( ph -> Z e. ( X I Y ) )


  assert |- ( ph -> ( Z e. ( X L Y ) \/ X = Y ) )

  proof
    wph
    cZ
    cX
    cY
    cL
    co
    wcel
    cX
    cY
    wceq
    wo
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
    @0
    @1
    @2
    btwncolg1.z
    3mix1d
    wph
    cP
    cG
    cI
    cL
    cX
    cY
    cZ
    tglngval.p
    tglngval.l
    tglngval.i
    tglngval.g
    tglngval.x
    tglngval.y
    tgcolg.z
    tgcolg
    mpbird
end
