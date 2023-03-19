include "wrex.mm"
include "crab.mm"
include "chash.mm"
include "cfv.mm"
include "ciun.mm"
include "csu.mm"
include "iunrab.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "hashiun.mm"
include "syl5eq.mm"

theorem hashrabrex
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  let cY: class Y
  assume hashrabrex.1: |- ( ph -> Y e. Fin )
  assume hashrabrex.2: |- ( ( ph /\ y e. Y ) -> { x e. X | ps } e. Fin )
  assume hashrabrex.3: |- ( ph -> Disj_ y e. Y { x e. X | ps } )

  disjoint X x
  disjoint X y
  disjoint x y
  disjoint Y x
  disjoint Y y
  disjoint ph y
  assert |- ( ph -> ( # ` { x e. X | E. y e. Y ps } ) = sum_ y e. Y ( # ` { x e. X | ps } ) )

  proof
    wph
    wps
    vy
    cY
    wrex
    vx
    cX
    crab
    #
    chash
    cfv
    vy
    cY
    wps
    vx
    cX
    crab
    #
    ciun
    #
    chash
    cfv
    cY
    @1
    chash
    cfv
    vy
    csu
    @0
    @2
    chash
    @2
    @0
    wps
    vy
    vx
    cY
    cX
    iunrab
    eqcomi
    fveq2i
    wph
    vy
    cY
    @1
    hashrabrex.1
    hashrabrex.2
    hashrabrex.3
    hashiun
    syl5eq
end
