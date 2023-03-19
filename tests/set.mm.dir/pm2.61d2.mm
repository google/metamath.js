include "wi.mm"
include "a1i.mm"
include "pm2.61d.mm"

theorem pm2.61d2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume pm2.61d2.1: |- ( ph -> ( -. ps -> ch ) )
  assume pm2.61d2.2: |- ( ps -> ch )


  assert |- ( ph -> ch )

  proof
    wph
    wps
    wch
    wps
    wch
    wi
    wph
    pm2.61d2.2
    a1i
    pm2.61d2.1
    pm2.61d
end
