include "wex.mm"
include "exbii.mm"
include "2exbii.mm"

theorem 3exbii
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume 3exbii.1: |- ( ph <-> ps )


  assert |- ( E. x E. y E. z ph <-> E. x E. y E. z ps )

  proof
    wph
    vz
    wex
    wps
    vz
    wex
    vx
    vy
    wph
    wps
    vz
    3exbii.1
    exbii
    2exbii
end
