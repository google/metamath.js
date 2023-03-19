include "mpd.mm"
include "wn.mm"
include "mpan2d.mm"
include "mt2d.mm"

theorem ex-natded5.8-2
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
    wta
    wth
    ex-natded5.8.4
    ex-natded5.8.2
    mpd
    wph
    wps
    wch
    wth
    wn
    ex-natded5.8.3
    ex-natded5.8.1
    mpan2d
    mt2d
end
