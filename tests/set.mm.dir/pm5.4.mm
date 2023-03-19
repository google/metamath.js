include "wi.mm"
include "pm2.43.mm"
include "ax-1.mm"
include "impbii.mm"

theorem pm5.4
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ( ph -> ps ) ) <-> ( ph -> ps ) )

  proof
    wph
    wph
    wps
    wi
    #
    wi
    @0
    wph
    wps
    pm2.43
    @0
    wph
    ax-1
    impbii
end
