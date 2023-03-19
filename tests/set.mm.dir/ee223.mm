include "wi.mm"
include "syl6.mm"
include "com34.mm"
include "com23.mm"
include "com12.mm"
include "syl8.mm"
include "pm2.43a.mm"
include "pm2.43d.mm"
include "mpdd.mm"

theorem ee223
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  assume ee223.1: |- ( ph -> ( ps -> ch ) )
  assume ee223.2: |- ( ph -> ( ps -> th ) )
  assume ee223.3: |- ( ph -> ( ps -> ( ta -> et ) ) )
  assume ee223.4: |- ( ch -> ( th -> ( et -> ze ) ) )


  assert |- ( ph -> ( ps -> ( ta -> ze ) ) )

  proof
    wph
    wps
    wth
    wta
    wze
    wi
    ee223.2
    wph
    wps
    wta
    wth
    wze
    wph
    wps
    wta
    wth
    wze
    wi
    #
    wi
    wph
    wps
    wta
    wps
    @0
    wps
    wph
    wta
    wps
    @0
    wi
    #
    wi
    wph
    wps
    wta
    wph
    @1
    wph
    wps
    wta
    wet
    wph
    @1
    wi
    ee223.3
    wph
    wet
    @1
    wph
    wps
    wet
    @0
    wph
    wps
    wth
    wet
    wze
    wph
    wps
    wch
    wth
    wet
    wze
    wi
    wi
    ee223.1
    ee223.4
    syl6
    com34
    com23
    com12
    syl8
    com34
    pm2.43a
    com34
    pm2.43d
    com34
    mpdd
end
