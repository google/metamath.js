include "pm2.21i.mm"
include "ax-mp.mm"

theorem pm2.24ii
  let wph: wff ph
  let wps: wff ps
  assume pm2.24ii.1: |- ph
  assume pm2.24ii.2: |- -. ph


  assert |- ps

  proof
    wph
    wps
    pm2.24ii.1
    wph
    wps
    pm2.24ii.2
    pm2.21i
    ax-mp
end
