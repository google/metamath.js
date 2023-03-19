include "wn.mm"
include "notnot.mm"
include "orri.mm"

theorem pm2.13
  let wph: wff ph


  assert |- ( ph \/ -. -. -. ph )

  proof
    wph
    wph
    wn
    #
    wn
    wn
    @0
    notnot
    orri
end
