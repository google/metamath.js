include "wn.mm"
include "id.mm"
include "con2i.mm"

theorem notnot
  let wph: wff ph


  assert |- ( ph -> -. -. ph )

  proof
    wph
    wn
    #
    wph
    @0
    id
    con2i
end
