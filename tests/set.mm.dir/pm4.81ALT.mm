include "wn.mm"
include "wi.mm"
include "pm2.18.mm"
include "ax-1.mm"
include "impbii.mm"

theorem pm4.81ALT
  let wph: wff ph


  assert |- ( ( -. ph -> ph ) <-> ph )

  proof
    wph
    wn
    #
    wph
    wi
    wph
    wph
    pm2.18
    wph
    @0
    ax-1
    impbii
end
