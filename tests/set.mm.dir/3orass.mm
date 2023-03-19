include "w3o.mm"
include "wo.mm"
include "df-3or.mm"
include "orass.mm"
include "bitri.mm"

theorem 3orass
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph \/ ps \/ ch ) <-> ( ph \/ ( ps \/ ch ) ) )

  proof
    wph
    wps
    wch
    w3o
    wph
    wps
    wo
    wch
    wo
    wph
    wps
    wch
    wo
    wo
    wph
    wps
    wch
    df-3or
    wph
    wps
    wch
    orass
    bitri
end
