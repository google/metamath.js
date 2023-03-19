include "wvd1.mm"
include "wi.mm"
include "df-vd1.mm"
include "biimpri.mm"

theorem dfvd1impr
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) -> (. ph ->. ps ). )

  proof
    wph
    wps
    wvd1
    wph
    wps
    wi
    wph
    wps
    df-vd1
    biimpri
end
