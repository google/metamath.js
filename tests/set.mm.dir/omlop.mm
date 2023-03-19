include "coml.mm"
include "wcel.mm"
include "col.mm"
include "cops.mm"
include "omlol.mm"
include "olop.mm"
include "syl.mm"

theorem omlop
  let cK: class K


  assert |- ( K e. OML -> K e. OP )

  proof
    cK
    coml
    wcel
    cK
    col
    wcel
    cK
    cops
    wcel
    cK
    omlol
    cK
    olop
    syl
end
