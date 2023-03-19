include "wex.mm"
include "eximi.mm"

theorem 2eximi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume eximi.1: |- ( ph -> ps )


  assert |- ( E. x E. y ph -> E. x E. y ps )

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
    eximi.1
    eximi
    eximi
end
