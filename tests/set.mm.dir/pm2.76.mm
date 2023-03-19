include "wi.mm"
include "wo.mm"
include "orimdi.mm"
include "biimpi.mm"

theorem pm2.76
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph \/ ( ps -> ch ) ) -> ( ( ph \/ ps ) -> ( ph \/ ch ) ) )

  proof
    wph
    wps
    wch
    wi
    wo
    wph
    wps
    wo
    wph
    wch
    wo
    wi
    wph
    wps
    wch
    orimdi
    biimpi
end
