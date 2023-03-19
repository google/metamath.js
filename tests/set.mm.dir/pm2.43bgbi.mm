include "wi.mm"
include "mercolem6.mm"
include "ax-1.mm"
include "impbii.mm"

theorem pm2.43bgbi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ( ps -> ( ph -> ch ) ) ) <-> ( ps -> ( ph -> ch ) ) )

  proof
    wph
    wps
    wph
    wch
    wi
    wi
    #
    wi
    @0
    wph
    wps
    wch
    mercolem6
    @0
    wph
    ax-1
    impbii
end
