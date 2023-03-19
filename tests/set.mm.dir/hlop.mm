include "chlt.mm"
include "wcel.mm"
include "col.mm"
include "cops.mm"
include "hlol.mm"
include "olop.mm"
include "syl.mm"

theorem hlop
  let cK: class K


  assert |- ( K e. HL -> K e. OP )

  proof
    cK
    chlt
    wcel
    cK
    col
    wcel
    cK
    cops
    wcel
    cK
    hlol
    cK
    olop
    syl
end
