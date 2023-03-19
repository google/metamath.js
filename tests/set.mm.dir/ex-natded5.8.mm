include "wa.mm"
include "adantr.mm"
include "wi.mm"
include "mpd.mm"
include "wn.mm"
include "simpr.mm"
include "jca.mm"
include "pm2.65da.mm"

theorem ex-natded5.8
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ex-natded5.8.1: |- ( ph -> ( ( ps /\ ch ) -> -. th ) )
  assume ex-natded5.8.2: |- ( ph -> ( ta -> th ) )
  assume ex-natded5.8.3: |- ( ph -> ch )
  assume ex-natded5.8.4: |- ( ph -> ta )


  assert |- ( ph -> -. ps )

  proof
    wph
    wps
    wth
    wph
    wps
    wa
    #
    wta
    wth
    wph
    wta
    wps
    ex-natded5.8.4
    adantr
    wph
    wta
    wth
    wi
    wps
    ex-natded5.8.2
    adantr
    mpd
    @0
    wps
    wch
    wa
    #
    wth
    wn
    #
    @0
    wps
    wch
    wph
    wps
    simpr
    wph
    wch
    wps
    ex-natded5.8.3
    adantr
    jca
    wph
    @1
    @2
    wi
    wps
    ex-natded5.8.1
    adantr
    mpd
    pm2.65da
end
