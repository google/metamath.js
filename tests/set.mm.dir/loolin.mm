include "wi.mm"
include "jarr.mm"
include "pm2.43d.mm"

theorem loolin
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ph -> ps ) -> ( ps -> ph ) ) -> ( ps -> ph ) )

  proof
    wph
    wps
    wi
    wps
    wph
    wi
    #
    wi
    wps
    wph
    wph
    wps
    @0
    jarr
    pm2.43d
end
