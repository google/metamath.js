include "cprrng.mm"
include "ccm2.mm"
include "cdmn.mm"
include "df-dmn.mm"
include "elin2.mm"

theorem isdmn
  let cR: class R


  assert |- ( R e. Dmn <-> ( R e. PrRing /\ R e. Com2 ) )

  proof
    cR
    cprrng
    ccm2
    cdmn
    df-dmn
    elin2
end
