include "wo.mm"
include "wn.mm"
include "wi.mm"
include "df-or.mm"
include "biimpri.mm"

theorem pm2.54
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( -. ph -> ps ) -> ( ph \/ ps ) )

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
    biimpri
end
