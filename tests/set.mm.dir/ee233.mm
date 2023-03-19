include "wi.mm"
include "syl6.mm"
include "com3r.mm"
include "syl8.mm"
include "pm2.43cbi.mm"
include "mpbi.mm"
include "com14.mm"

theorem ee233
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  assume ee233.1: |- ( ph -> ( ps -> ch ) )
  assume ee233.2: |- ( ph -> ( ps -> ( th -> ta ) ) )
  assume ee233.3: |- ( ph -> ( ps -> ( th -> et ) ) )
  assume ee233.4: |- ( ch -> ( ta -> ( et -> ze ) ) )


  assert |- ( ph -> ( ps -> ( th -> ze ) ) )

  proof
    wth
    wph
    wps
    wth
    wze
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
    @4
    wph
    wps
    wth
    wet
    @2
    ee233.3
    wth
    wph
    wps
    wet
    wze
    wps
    wth
    wph
    wps
    wet
    wze
    wi
    #
    wi
    #
    wi
    #
    wi
    #
    wi
    #
    @8
    wph
    @9
    wi
    @9
    wph
    wps
    wth
    wta
    @7
    ee233.2
    wph
    wps
    wta
    @5
    wph
    wps
    wch
    wta
    @5
    wi
    ee233.1
    ee233.4
    syl6
    com3r
    syl8
    wph
    wps
    wth
    @6
    pm2.43cbi
    mpbi
    wps
    wth
    wph
    @5
    pm2.43cbi
    mpbi
    com14
    syl8
    wph
    wps
    wth
    @1
    pm2.43cbi
    mpbi
    wps
    wth
    wph
    @0
    pm2.43cbi
    mpbi
    wth
    wph
    wps
    wze
    pm2.43cbi
    mpbi
end
