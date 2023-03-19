include "wi.mm"
include "wo.mm"
include "pm2.76.mm"
include "com12.mm"

theorem pm2.75
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph \/ ps ) -> ( ( ph \/ ( ps -> ch ) ) -> ( ph \/ ch ) ) )

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
    wph
    wps
    wch
    pm2.76
    com12
end
