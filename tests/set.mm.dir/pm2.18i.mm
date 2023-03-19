include "wn.mm"
include "wi.mm"
include "pm2.18.mm"
include "ax-mp.mm"

theorem pm2.18i
  let wph: wff ph
  assume pm2.18i.1: |- ( -. ph -> ph )


  assert |- ph

  proof
    wph
    wn
    wph
    wi
    wph
    pm2.18i.1
    wph
    pm2.18
    ax-mp
end
