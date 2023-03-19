include "wo.mm"
include "wi.mm"
include "pm1.4.mm"
include "pm2.38.mm"
include "syl5.mm"

theorem pm2.36
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ps -> ch ) -> ( ( ph \/ ps ) -> ( ch \/ ph ) ) )

  proof
    wph
    wps
    wo
    wps
    wph
    wo
    wps
    wch
    wi
    wch
    wph
    wo
    wph
    wps
    pm1.4
    wph
    wps
    wch
    pm2.38
    syl5
end
