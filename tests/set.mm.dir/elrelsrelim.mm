include "crels.mm"
include "wcel.mm"
include "wrel.mm"
include "elrelsrel.mm"
include "ibi.mm"

theorem elrelsrelim
  let cR: class R


  assert |- ( R e. Rels -> Rel R )

  proof
    cR
    crels
    wcel
    cR
    wrel
    cR
    crels
    elrelsrel
    ibi
end
