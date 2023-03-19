include "cv.mm"
include "wbr.mm"
include "copab.mm"
include "wa.mm"
include "cvv.mm"
include "pm4.24.mm"
include "opabbii.mm"
include "opabresex0d.mm"
include "syl5eqel.mm"

theorem opabbrfex0d
  let wph: wff ph
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cR: class R
  let cV: class V
  let cW: class W
  let vk: setvar k
  assume opabresex0d.x: |- ( ( ph /\ x R y ) -> x e. C )
  assume opabresex0d.t: |- ( ( ph /\ x R y ) -> th )
  assume opabresex0d.y: |- ( ( ph /\ x e. C ) -> { y | th } e. V )
  assume opabresex0d.c: |- ( ph -> C e. W )

  disjoint C x
  disjoint C y
  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint k x
  assert |- ( ph -> { <. x , y >. | x R y } e. _V )

  proof
    wph
    vx
    cv
    vy
    cv
    cR
    wbr
    #
    vx
    vy
    copab
    @0
    @0
    wa
    #
    vx
    vy
    copab
    cvv
    @0
    @1
    vx
    vy
    @0
    pm4.24
    opabbii
    wph
    @0
    wth
    vx
    vy
    cC
    cR
    cV
    cW
    opabresex0d.x
    opabresex0d.t
    opabresex0d.y
    opabresex0d.c
    opabresex0d
    syl5eqel
end
