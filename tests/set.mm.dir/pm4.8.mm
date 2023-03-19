include "wn.mm"
include "wi.mm"
include "pm2.01.mm"
include "ax-1.mm"
include "impbii.mm"

theorem pm4.8
  let wph: wff ph


  assert |- ( ( ph -> -. ph ) <-> -. ph )

  proof
    wph
    wph
    wn
    #
    wi
    @0
    wph
    pm2.01
    @0
    wph
    ax-1
    impbii
end
