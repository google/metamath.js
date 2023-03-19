include "wn.mm"
include "con1d.mm"
include "mpd.mm"

theorem mt3d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume mt3d.1: |- ( ph -> -. ch )
  assume mt3d.2: |- ( ph -> ( -. ps -> ch ) )


  assert |- ( ph -> ps )

  proof
    wph
    wch
    wn
    wps
    mt3d.1
    wph
    wps
    wch
    mt3d.2
    con1d
    mpd
end
