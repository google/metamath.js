include "wa.mm"
include "wex.mm"
include "exdistr.mm"
include "19.42v.mm"
include "bitri.mm"

theorem 19.42vv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y

  disjoint ph x
  disjoint ph y
  assert |- ( E. x E. y ( ph /\ ps ) <-> ( ph /\ E. x E. y ps ) )

  proof
    wph
    wps
    wa
    vy
    wex
    vx
    wex
    wph
    wps
    vy
    wex
    #
    wa
    vx
    wex
    wph
    @0
    vx
    wex
    wa
    wph
    wps
    vx
    vy
    exdistr
    wph
    @0
    vx
    19.42v
    bitri
end
