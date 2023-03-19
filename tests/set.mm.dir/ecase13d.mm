include "wn.mm"
include "wo.mm"
include "wi.mm"
include "w3o.mm"
include "3orass.mm"
include "df-or.mm"
include "bitri.mm"
include "sylib.mm"
include "mpd.mm"
include "orcom.mm"

theorem ecase13d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume ecase13d.1: |- ( ph -> -. ch )
  assume ecase13d.2: |- ( ph -> -. th )
  assume ecase13d.3: |- ( ph -> ( ch \/ ps \/ th ) )


  assert |- ( ph -> ps )

  proof
    wph
    wth
    wn
    #
    wps
    ecase13d.2
    wph
    wps
    wth
    wo
    #
    @0
    wps
    wi
    #
    wph
    wch
    wn
    #
    @1
    ecase13d.1
    wph
    wch
    wps
    wth
    w3o
    #
    @3
    @1
    wi
    #
    ecase13d.3
    @4
    wch
    @1
    wo
    @5
    wch
    wps
    wth
    3orass
    wch
    @1
    df-or
    bitri
    sylib
    mpd
    @1
    wth
    wps
    wo
    @2
    wps
    wth
    orcom
    wth
    wps
    df-or
    bitri
    sylib
    mpd
end
