include "pm2.21d.mm"
include "mpd.mm"

theorem pm2.21ddALT
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume pm2.21ddALT.1: |- ( ph -> ps )
  assume pm2.21ddALT.2: |- ( ph -> -. ps )


  assert |- ( ph -> ch )

  proof
    wph
    wps
    wch
    pm2.21ddALT.1
    wph
    wps
    wch
    pm2.21ddALT.2
    pm2.21d
    mpd
end
