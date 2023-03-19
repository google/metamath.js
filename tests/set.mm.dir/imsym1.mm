include "wfal.mm"
include "wi.mm"
include "pm2.21.mm"
include "falim.mm"
include "imim2i.mm"
include "ja.mm"

theorem imsym1
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ps -> ( ps -> F. ) ) -> ( ps -> ph ) )

  proof
    wps
    wps
    wfal
    wi
    wps
    wph
    wi
    wps
    wph
    pm2.21
    wfal
    wph
    wps
    wph
    falim
    imim2i
    ja
end
