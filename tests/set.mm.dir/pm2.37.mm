include "wi.mm"
include "wo.mm"
include "pm2.38.mm"
include "pm1.4.mm"
include "syl6.mm"

theorem pm2.37
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ps -> ch ) -> ( ( ps \/ ph ) -> ( ph \/ ch ) ) )

  proof
    wps
    wch
    wi
    wps
    wph
    wo
    wch
    wph
    wo
    wph
    wch
    wo
    wph
    wps
    wch
    pm2.38
    wch
    wph
    pm1.4
    syl6
end
