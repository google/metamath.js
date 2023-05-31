include "wo.mm"
include "wn.mm"
include "wi.mm"
include "df-or.mm"
include "biimpi.mm"

theorem pm2.53
  param wph: wff ph
  param wps: wff ps


  assert |- ( ( ph \/ ps ) -> ( -. ph -> ps ) )

  proof
    wph
    wps
    wo
    wph
    wn
    wps
    wi
    wph
    wps
    df-or
    biimpi
end
