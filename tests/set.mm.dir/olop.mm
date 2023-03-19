include "col.mm"
include "wcel.mm"
include "clat.mm"
include "cops.mm"
include "isolat.mm"
include "simprbi.mm"

theorem olop
  let cK: class K


  assert |- ( K e. OL -> K e. OP )

  proof
    cK
    col
    wcel
    cK
    clat
    wcel
    cK
    cops
    wcel
    cK
    isolat
    simprbi
end
