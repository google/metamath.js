include "chlt.mm"
include "wcel.mm"
include "coml.mm"
include "col.mm"
include "hloml.mm"
include "omlol.mm"
include "syl.mm"

theorem hlol
  let cK: class K


  assert |- ( K e. HL -> K e. OL )

  proof
    cK
    chlt
    wcel
    cK
    coml
    wcel
    cK
    col
    wcel
    cK
    hloml
    cK
    omlol
    syl
end
