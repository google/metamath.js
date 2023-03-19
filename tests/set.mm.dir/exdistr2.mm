include "wa.mm"
include "wex.mm"
include "19.42vv.mm"
include "exbii.mm"

theorem exdistr2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint ph y
  disjoint ph z
  assert |- ( E. x E. y E. z ( ph /\ ps ) <-> E. x ( ph /\ E. y E. z ps ) )

  proof
    wph
    wps
    wa
    vz
    wex
    vy
    wex
    wph
    wps
    vz
    wex
    vy
    wex
    wa
    vx
    wph
    wps
    vy
    vz
    19.42vv
    exbii
end
