include "wn.mm"
include "pm2.61d2.mm"
include "pm2.61i.mm"

theorem pm2.61ii
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume pm2.61ii.1: |- ( -. ph -> ( -. ps -> ch ) )
  assume pm2.61ii.2: |- ( ph -> ch )
  assume pm2.61ii.3: |- ( ps -> ch )


  assert |- ch

  proof
    wph
    wch
    pm2.61ii.2
    wph
    wn
    wps
    wch
    pm2.61ii.1
    pm2.61ii.3
    pm2.61d2
    pm2.61i
end
