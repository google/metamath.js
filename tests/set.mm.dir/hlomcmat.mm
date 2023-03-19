include "chlt.mm"
include "wcel.mm"
include "coml.mm"
include "ccla.mm"
include "cal.mm"
include "hloml.mm"
include "hlclat.mm"
include "hlatl.mm"
include "3jca.mm"

theorem hlomcmat
  let cK: class K


  assert |- ( K e. HL -> ( K e. OML /\ K e. CLat /\ K e. AtLat ) )

  proof
    cK
    chlt
    wcel
    cK
    coml
    wcel
    cK
    ccla
    wcel
    cK
    cal
    wcel
    cK
    hloml
    cK
    hlclat
    cK
    hlatl
    3jca
end
