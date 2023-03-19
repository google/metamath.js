include "wa.mm"
include "wex.mm"
include "19.42v.mm"
include "exbii.mm"

theorem exdistr
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y

  disjoint ph y
  assert |- ( E. x E. y ( ph /\ ps ) <-> E. x ( ph /\ E. y ps ) )

  proof
    wph
    wps
    wa
    vy
    wex
    wph
    wps
    vy
    wex
    wa
    vx
    wph
    wps
    vy
    19.42v
    exbii
end
