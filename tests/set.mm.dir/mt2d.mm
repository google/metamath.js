include "wn.mm"
include "con2d.mm"
include "mpd.mm"

theorem mt2d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume mt2d.1: |- ( ph -> ch )
  assume mt2d.2: |- ( ph -> ( ps -> -. ch ) )


  assert |- ( ph -> -. ps )

  proof
    wph
    wch
    wps
    wn
    mt2d.1
    wph
    wps
    wch
    mt2d.2
    con2d
    mpd
end
