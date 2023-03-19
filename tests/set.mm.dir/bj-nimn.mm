include "wn.mm"
include "wi.mm"
include "pm2.01.mm"
include "con2i.mm"

theorem bj-nimn
  let wph: wff ph


  assert |- ( ph -> -. ( ph -> -. ph ) )

  proof
    wph
    wph
    wn
    wi
    wph
    wph
    pm2.01
    con2i
end
