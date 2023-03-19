include "con4d.mm"
include "mpd.mm"

theorem mt4d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume mt4d.1: |- ( ph -> ps )
  assume mt4d.2: |- ( ph -> ( -. ch -> -. ps ) )


  assert |- ( ph -> ch )

  proof
    wph
    wps
    wch
    mt4d.1
    wph
    wch
    wps
    mt4d.2
    con4d
    mpd
end
