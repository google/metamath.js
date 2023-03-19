include "wa.mm"
include "simpr.mm"
include "wi.mm"
include "adantr.mm"
include "mpd.mm"
include "jca.mm"
include "ex.mm"

theorem ex-natded5.3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume ex-natded5.3.1: |- ( ph -> ( ps -> ch ) )
  assume ex-natded5.3.2: |- ( ph -> ( ch -> th ) )


  assert |- ( ph -> ( ps -> ( ch /\ th ) ) )

  proof
    wph
    wps
    wch
    wth
    wa
    wph
    wps
    wa
    #
    wch
    wth
    @0
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
    ex-natded5.3.1
    adantr
    mpd
    #
    @0
    wch
    wth
    @1
    wph
    wch
    wth
    wi
    wps
    ex-natded5.3.2
    adantr
    mpd
    jca
    ex
end
