include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "wrdf.mm"
include "ffvelrnda.mm"

theorem wrdsymbcl
  let cI: class I
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ I e. ( 0 ..^ ( # ` W ) ) ) -> ( W ` I ) e. V )

  proof
    cW
    cV
    cword
    wcel
    cc0
    cW
    chash
    cfv
    cfzo
    co
    cV
    cI
    cW
    cV
    cW
    wrdf
    ffvelrnda
end
