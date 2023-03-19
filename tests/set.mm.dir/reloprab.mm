include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "coprab.mm"
include "dfoprab2.mm"
include "relopabi.mm"

theorem reloprab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v

  disjoint x z
  disjoint y z
  disjoint w x
  disjoint v x
  disjoint w z
  disjoint v z
  disjoint v w
  disjoint w y
  disjoint v y
  disjoint ph w
  disjoint ph v
  assert |- Rel { <. <. x , y >. , z >. | ph }

  proof
    vw
    cv
    vx
    cv
    vy
    cv
    cop
    wceq
    wph
    wa
    vy
    wex
    vx
    wex
    vw
    vz
    wph
    vx
    vy
    vz
    coprab
    wph
    vx
    vy
    vz
    vw
    dfoprab2
    relopabi
end
