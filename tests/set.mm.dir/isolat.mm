include "clat.mm"
include "cops.mm"
include "col.mm"
include "df-ol.mm"
include "elin2.mm"

theorem isolat
  let cK: class K


  assert |- ( K e. OL <-> ( K e. Lat /\ K e. OP ) )

  proof
    cK
    clat
    cops
    col
    df-ol
    elin2
end
