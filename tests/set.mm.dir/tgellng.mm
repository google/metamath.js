include "co.mm"
include "wcel.mm"
include "w3o.mm"
include "wa.mm"
include "cv.mm"
include "crab.mm"
include "tglngval.mm"
include "eleq2d.mm"
include "wceq.mm"
include "eleq1.mm"
include "oveq1.mm"
include "oveq2.mm"
include "3orbi123d.mm"
include "elrab.mm"
include "syl6bb.mm"
include "biantrurd.mm"
include "bitr4d.mm"

theorem tgellng
  let wph: wff ph
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vz: setvar z
  let vx: setvar x
  let vy: setvar y
  assume tglngval.p: |- P = ( Base ` G )
  assume tglngval.l: |- L = ( LineG ` G )
  assume tglngval.i: |- I = ( Itv ` G )
  assume tglngval.g: |- ( ph -> G e. TarskiG )
  assume tglngval.x: |- ( ph -> X e. P )
  assume tglngval.y: |- ( ph -> Y e. P )
  assume tglngval.z: |- ( ph -> X =/= Y )
  assume tgellng.z: |- ( ph -> Z e. P )


  assert |- ( ph -> ( Z e. ( X L Y ) <-> ( Z e. ( X I Y ) \/ X e. ( Z I Y ) \/ Y e. ( X I Z ) ) ) )

  proof
    wph
    cZ
    cX
    cY
    cL
    co
    #
    wcel
    #
    cZ
    cP
    wcel
    #
    cZ
    cX
    cY
    cI
    co
    #
    wcel
    #
    cX
    cZ
    cY
    cI
    co
    #
    wcel
    #
    cY
    cX
    cZ
    cI
    co
    #
    wcel
    #
    w3o
    #
    wa
    #
    @9
    wph
    @1
    cZ
    vz
    cv
    #
    @3
    wcel
    #
    cX
    @11
    cY
    cI
    co
    #
    wcel
    #
    cY
    cX
    @11
    cI
    co
    #
    wcel
    #
    w3o
    #
    vz
    cP
    crab
    #
    wcel
    @10
    wph
    @0
    @18
    cZ
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
    eleq2d
    @17
    @9
    vz
    cZ
    cP
    @11
    cZ
    wceq
    #
    @12
    @4
    @14
    @6
    @16
    @8
    @11
    cZ
    @3
    eleq1
    @19
    @13
    @5
    cX
    @11
    cZ
    cY
    cI
    oveq1
    eleq2d
    @19
    @15
    @7
    cY
    @11
    cZ
    cX
    cI
    oveq2
    eleq2d
    3orbi123d
    elrab
    syl6bb
    wph
    @2
    @9
    tgellng.z
    biantrurd
    bitr4d
end
