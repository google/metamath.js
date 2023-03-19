include "wn.mm"
include "wi.mm"
include "pm2.18.mm"
include "pm2.24.mm"
include "impbii.mm"

theorem pm4.81
  let wph: wff ph


  assert |- ( ( -. ph -> ph ) <-> ph )

  proof
    wph
    wn
    wph
    wi
    wph
    wph
    pm2.18
    wph
    wph
    pm2.24
    impbii
end
