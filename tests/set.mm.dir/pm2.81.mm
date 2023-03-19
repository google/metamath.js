include "wi.mm"
include "wo.mm"
include "orim2.mm"
include "pm2.76.mm"
include "syl6.mm"

theorem pm2.81
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ps -> ( ch -> th ) ) -> ( ( ph \/ ps ) -> ( ( ph \/ ch ) -> ( ph \/ th ) ) ) )

  proof
    wps
    wch
    wth
    wi
    #
    wi
    wph
    wps
    wo
    wph
    @0
    wo
    wph
    wch
    wo
    wph
    wth
    wo
    wi
    wph
    wps
    @0
    orim2
    wph
    wch
    wth
    pm2.76
    syl6
end
