include "wo.mm"
include "wa.mm"
include "simpr.mm"
include "wi.mm"
include "adantr.mm"
include "mpd.mm"
include "orcd.mm"
include "wn.mm"
include "ad2antrr.mm"
include "pm2.65da.mm"
include "notnotrd.mm"
include "olcd.mm"
include "mpjaodan.mm"

theorem ex-natded5.13
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ex-natded5.13.1: |- ( ph -> ( ps \/ ch ) )
  assume ex-natded5.13.2: |- ( ph -> ( ps -> th ) )
  assume ex-natded5.13.3: |- ( ph -> ( -. ta -> -. ch ) )


  assert |- ( ph -> ( th \/ ta ) )

  proof
    wph
    wps
    wth
    wta
    wo
    wch
    wph
    wps
    wa
    #
    wth
    wta
    @0
    wps
    wth
    wph
    wps
    simpr
    wph
    wps
    wth
    wi
    wps
    ex-natded5.13.2
    adantr
    mpd
    orcd
    wph
    wch
    wa
    #
    wta
    wth
    @1
    wta
    @1
    wta
    wn
    #
    wch
    @1
    wch
    @2
    wph
    wch
    simpr
    adantr
    @1
    @2
    wa
    @2
    wch
    wn
    #
    @1
    @2
    simpr
    wph
    @2
    @3
    wi
    wch
    @2
    ex-natded5.13.3
    ad2antrr
    mpd
    pm2.65da
    notnotrd
    olcd
    ex-natded5.13.1
    mpjaodan
end
