include "wo.mm"
include "con4d.mm"
include "orim12d.mm"
include "mpd.mm"

theorem ex-natded5.13-2
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
    wch
    wo
    wth
    wta
    wo
    ex-natded5.13.1
    wph
    wps
    wth
    wch
    wta
    ex-natded5.13.2
    wph
    wta
    wch
    ex-natded5.13.3
    con4d
    orim12d
    mpd
end
