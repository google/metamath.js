include "wex.mm"
include "exbii.mm"

theorem 2exbii
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume 2exbii.1: |- ( ph <-> ps )


  assert |- ( E. x E. y ph <-> E. x E. y ps )

  proof
    wph
    vy
    wex
    wps
    vy
    wex
    vx
    wph
    wps
    vy
    2exbii.1
    exbii
    exbii
end
