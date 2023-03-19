include "wex.mm"
include "cv.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "cp.mm"
include "ralim.mm"
include "eximii.mm"
include "19.37iv.mm"

theorem bnd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint ph z
  disjoint ph w
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  assert |- ( A. x e. z E. y ph -> E. w A. x e. z E. y e. w ph )

  proof
    wph
    vy
    wex
    #
    vx
    vz
    cv
    #
    wral
    #
    wph
    vy
    vw
    cv
    wrex
    #
    vx
    @1
    wral
    #
    vw
    @0
    @3
    wi
    vx
    @1
    wral
    @2
    @4
    wi
    vw
    wph
    vx
    vy
    vz
    vw
    cp
    @0
    @3
    vx
    @1
    ralim
    eximii
    19.37iv
end
