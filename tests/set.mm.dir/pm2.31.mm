include "wo.mm"
include "orass.mm"
include "biimpri.mm"

theorem pm2.31
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph \/ ( ps \/ ch ) ) -> ( ( ph \/ ps ) \/ ch ) )

  proof
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
    orass
    biimpri
end
