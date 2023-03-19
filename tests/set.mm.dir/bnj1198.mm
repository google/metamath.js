include "wex.mm"
include "exbii.mm"
include "sylibr.mm"

theorem bnj1198
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let bnjwpsm: wff ps'
  assume bnj1198.1: |- ( ph -> E. x ps )
  assume bnj1198.2: |- ( ps' <-> ps )


  assert |- ( ph -> E. x ps' )

  proof
    wph
    wps
    vx
    wex
    bnjwpsm
    vx
    wex
    bnj1198.1
    bnjwpsm
    wps
    vx
    bnj1198.2
    exbii
    sylibr
end
