include "wn.mm"
include "con1d.mm"
include "syld.mm"
include "pm2.18d.mm"

theorem pm2.61d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume pm2.61d.1: |- ( ph -> ( ps -> ch ) )
  assume pm2.61d.2: |- ( ph -> ( -. ps -> ch ) )


  assert |- ( ph -> ch )

  proof
    wph
    wch
    wph
    wch
    wn
    wps
    wch
    wph
    wps
    wch
    pm2.61d.2
    con1d
    pm2.61d.1
    syld
    pm2.18d
end
