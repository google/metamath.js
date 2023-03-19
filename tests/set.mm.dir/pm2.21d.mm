include "wn.mm"
include "a1d.mm"
include "con4d.mm"

theorem pm2.21d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume pm2.21d.1: |- ( ph -> -. ps )


  assert |- ( ph -> ( ps -> ch ) )

  proof
    wph
    wch
    wps
    wph
    wps
    wn
    wch
    wn
    pm2.21d.1
    a1d
    con4d
end
