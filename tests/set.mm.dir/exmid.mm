include "wn.mm"
include "id.mm"
include "orri.mm"

theorem exmid
  param wph: wff ph


  assert |- ( ph \/ -. ph )

  proof
    wph
    wph
    wn
    #
    @0
    id
    orri
end
