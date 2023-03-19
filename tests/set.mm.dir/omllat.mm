include "coml.mm"
include "wcel.mm"
include "col.mm"
include "clat.mm"
include "omlol.mm"
include "ollat.mm"
include "syl.mm"

theorem omllat
  let cK: class K


  assert |- ( K e. OML -> K e. Lat )

  proof
    cK
    coml
    wcel
    cK
    col
    wcel
    cK
    clat
    wcel
    cK
    omlol
    cK
    ollat
    syl
end
