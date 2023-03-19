include "wo.mm"
include "wn.mm"
include "pm1.2.mm"
include "con3i.mm"
include "con1i.mm"
include "orri.mm"

theorem rb-ax4
  let wph: wff ph


  assert |- ( -. ( ph \/ ph ) \/ ph )

  proof
    wph
    wph
    wo
    #
    wn
    #
    wph
    wph
    @1
    @0
    wph
    wph
    pm1.2
    con3i
    con1i
    orri
end
