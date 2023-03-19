include "cop.mm"
include "cco.mm"
include "cfv.mm"
include "co.mm"
include "ctpos.mm"
include "oppccofval.mm"
include "oveqd.mm"
include "ovtpos.mm"
include "syl6eq.mm"

theorem oppcco
  let wph: wff ph
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cO: class O
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vu: setvar u
  let vz: setvar z
  assume oppcco.b: |- B = ( Base ` C )
  assume oppcco.c: |- .x. = ( comp ` C )
  assume oppcco.o: |- O = ( oppCat ` C )
  assume oppcco.x: |- ( ph -> X e. B )
  assume oppcco.y: |- ( ph -> Y e. B )
  assume oppcco.z: |- ( ph -> Z e. B )


  assert |- ( ph -> ( G ( <. X , Y >. ( comp ` O ) Z ) F ) = ( F ( <. Z , Y >. .x. X ) G ) )

  proof
    wph
    cG
    cF
    cX
    cY
    cop
    cZ
    cO
    cco
    cfv
    co
    #
    co
    cG
    cF
    cZ
    cY
    cop
    cX
    c.x
    co
    #
    ctpos
    #
    co
    cF
    cG
    @1
    co
    wph
    @0
    @2
    cG
    cF
    wph
    cB
    cC
    c.x
    cO
    cX
    cY
    cZ
    oppcco.b
    oppcco.c
    oppcco.o
    oppcco.x
    oppcco.y
    oppcco.z
    oppccofval
    oveqd
    cG
    cF
    @1
    ovtpos
    syl6eq
end
