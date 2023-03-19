include "wn.mm"
include "a1d.mm"
include "pm2.65d.mm"

theorem mtod
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume mtod.1: |- ( ph -> -. ch )
  assume mtod.2: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> -. ps )

  proof
    wph
    wps
    wch
    mtod.2
    wph
    wch
    wn
    wps
    mtod.1
    a1d
    pm2.65d
end
