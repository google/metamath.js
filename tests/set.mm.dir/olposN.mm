include "col.mm"
include "wcel.mm"
include "cops.mm"
include "cpo.mm"
include "olop.mm"
include "opposet.mm"
include "syl.mm"

theorem olposN
  let cK: class K


  assert |- ( K e. OL -> K e. Poset )

  proof
    cK
    col
    wcel
    cK
    cops
    wcel
    cK
    cpo
    wcel
    cK
    olop
    cK
    opposet
    syl
end
