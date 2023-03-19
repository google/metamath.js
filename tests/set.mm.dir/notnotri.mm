include "wn.mm"
include "pm2.21i.mm"
include "pm2.18i.mm"

theorem notnotri
  let wph: wff ph
  assume notnotri.1: |- -. -. ph


  assert |- ph

  proof
    wph
    wph
    wn
    wph
    notnotri.1
    pm2.21i
    pm2.18i
end
