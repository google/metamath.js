include "wex.mm"
include "wa.mm"
include "19.41v.mm"
include "sylibr.mm"

theorem bnj534
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume bnj534.1: |- ( ch -> ( E. x ph /\ ps ) )

  disjoint ps x
  assert |- ( ch -> E. x ( ph /\ ps ) )

  proof
    wch
    wph
    vx
    wex
    wps
    wa
    wph
    wps
    wa
    vx
    wex
    bnj534.1
    wph
    wps
    vx
    19.41v
    sylibr
end
