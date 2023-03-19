include "wo.mm"
include "wex.mm"
include "19.43.mm"
include "19.9v.mm"
include "orbi1i.mm"
include "bitri.mm"

theorem 19.45v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x

  disjoint ph x
  assert |- ( E. x ( ph \/ ps ) <-> ( ph \/ E. x ps ) )

  proof
    wph
    wps
    wo
    vx
    wex
    wph
    vx
    wex
    #
    wps
    vx
    wex
    #
    wo
    wph
    @1
    wo
    wph
    wps
    vx
    19.43
    @0
    wph
    @1
    wph
    vx
    19.9v
    orbi1i
    bitri
end
