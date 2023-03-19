include "col.mm"
include "wcel.mm"
include "clat.mm"
include "cops.mm"
include "isolat.mm"
include "simplbi.mm"

theorem ollat
  let cK: class K


  assert |- ( K e. OL -> K e. Lat )

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
    simplbi
end
