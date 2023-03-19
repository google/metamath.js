include "wi.mm"
include "wn.mm"
include "pm2.24.mm"
include "com4l.mm"
include "id.mm"
include "ja.mm"
include "ax-1.mm"
include "impbii.mm"

theorem pm2.43cbi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -> ( ps -> ( ch -> ( ph -> th ) ) ) ) <-> ( ps -> ( ch -> ( ph -> th ) ) ) )

  proof
    wph
    wps
    wch
    wph
    wth
    wi
    wi
    wi
    #
    wi
    @0
    wph
    @0
    @0
    wph
    wph
    wn
    wps
    wch
    wth
    wph
    wps
    wch
    wth
    wi
    wi
    pm2.24
    com4l
    @0
    id
    ja
    @0
    wph
    ax-1
    impbii
end
