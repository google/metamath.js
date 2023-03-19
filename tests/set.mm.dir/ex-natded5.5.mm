include "wa.mm"
include "simpr.mm"
include "wi.mm"
include "adantr.mm"
include "mpd.mm"
include "wn.mm"
include "pm2.65da.mm"

theorem ex-natded5.5
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume ex-natded5.5.1: |- ( ph -> ( ps -> ch ) )
  assume ex-natded5.5.2: |- ( ph -> -. ch )


  assert |- ( ph -> -. ps )

  proof
    wph
    wps
    wch
    wph
    wps
    wa
    wps
    wch
    wph
    wps
    simpr
    wph
    wps
    wch
    wi
    wps
    ex-natded5.5.1
    adantr
    mpd
    wph
    wch
    wn
    wps
    ex-natded5.5.2
    adantr
    pm2.65da
end
