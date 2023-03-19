include "wn.mm"
include "wi.mm"
include "a1d.mm"
include "pm2.61ii.mm"
include "pm2.61i.mm"

theorem pm2.61iii
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume pm2.61iii.1: |- ( -. ph -> ( -. ps -> ( -. ch -> th ) ) )
  assume pm2.61iii.2: |- ( ph -> th )
  assume pm2.61iii.3: |- ( ps -> th )
  assume pm2.61iii.4: |- ( ch -> th )


  assert |- th

  proof
    wch
    wth
    pm2.61iii.4
    wph
    wps
    wch
    wn
    #
    wth
    wi
    pm2.61iii.1
    wph
    wth
    @0
    pm2.61iii.2
    a1d
    wps
    wth
    @0
    pm2.61iii.3
    a1d
    pm2.61ii
    pm2.61i
end
