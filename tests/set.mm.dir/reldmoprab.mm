include "wex.mm"
include "coprab.mm"
include "cdm.mm"
include "dmoprab.mm"
include "relopabi.mm"

theorem reldmoprab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  disjoint y z
  assert |- Rel dom { <. <. x , y >. , z >. | ph }

  proof
    wph
    vz
    wex
    vx
    vy
    wph
    vx
    vy
    vz
    coprab
    cdm
    wph
    vx
    vy
    vz
    dmoprab
    relopabi
end
