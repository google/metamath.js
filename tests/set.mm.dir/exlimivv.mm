include "wex.mm"
include "exlimiv.mm"

theorem exlimivv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume exlimivv.1: |- ( ph -> ps )

  disjoint ps x
  disjoint ps y
  assert |- ( E. x E. y ph -> ps )

  proof
    wph
    vy
    wex
    wps
    vx
    wph
    wps
    vy
    exlimivv.1
    exlimiv
    exlimiv
end
