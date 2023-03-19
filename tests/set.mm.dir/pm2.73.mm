include "wi.mm"
include "wo.mm"
include "pm2.621.mm"
include "orim1d.mm"

theorem pm2.73
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ps ) -> ( ( ( ph \/ ps ) \/ ch ) -> ( ps \/ ch ) ) )

  proof
    wph
    wps
    wi
    wph
    wps
    wo
    wps
    wch
    wph
    wps
    pm2.621
    orim1d
end
