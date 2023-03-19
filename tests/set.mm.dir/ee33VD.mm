include "wi.mm"
include "syl8.mm"
include "com4r.mm"
include "pm2.43cbi.mm"
include "biimpi.mm"
include "e0a.mm"

theorem ee33VD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee33VD.1: |- ( ph -> ( ps -> ( ch -> th ) ) )
  assume ee33VD.2: |- ( ph -> ( ps -> ( ch -> ta ) ) )
  assume ee33VD.3: |- ( th -> ( ta -> et ) )


  assert |- ( ph -> ( ps -> ( ch -> et ) ) )

  proof
    wch
    wph
    wps
    wch
    wet
    wi
    #
    wi
    #
    wi
    #
    wi
    #
    @2
    wps
    @3
    wi
    #
    @3
    wph
    @4
    wi
    #
    @4
    wph
    wps
    wch
    wta
    @2
    ee33VD.2
    wph
    wps
    wch
    wta
    wet
    wph
    wps
    wch
    wth
    wta
    wet
    wi
    ee33VD.1
    ee33VD.3
    syl8
    com4r
    syl8
    @5
    @4
    wph
    wps
    wch
    @1
    pm2.43cbi
    biimpi
    e0a
    @4
    @3
    wps
    wch
    wph
    @0
    pm2.43cbi
    biimpi
    e0a
    @3
    @2
    wch
    wph
    wps
    wet
    pm2.43cbi
    biimpi
    e0a
end
