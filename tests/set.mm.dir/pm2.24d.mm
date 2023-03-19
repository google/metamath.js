include "wn.mm"
include "a1d.mm"
include "con1d.mm"

theorem pm2.24d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume pm2.24d.1: |- ( ph -> ps )


  assert |- ( ph -> ( -. ps -> ch ) )

  proof
    wph
    wch
    wps
    wph
    wps
    wch
    wn
    pm2.24d.1
    a1d
    con1d
end
