include "cz.mm"
include "wcel.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "zre.mm"
include "letr.mm"
include "syl3an.mm"

theorem zletr
  let cJ: class J
  let cK: class K
  let cL: class L


  assert |- ( ( J e. ZZ /\ K e. ZZ /\ L e. ZZ ) -> ( ( J <_ K /\ K <_ L ) -> J <_ L ) )

  proof
    cJ
    cz
    wcel
    cJ
    cr
    wcel
    cK
    cz
    wcel
    cK
    cr
    wcel
    cL
    cz
    wcel
    cL
    cr
    wcel
    cJ
    cK
    cle
    wbr
    cK
    cL
    cle
    wbr
    wa
    cJ
    cL
    cle
    wbr
    wi
    cJ
    zre
    cK
    zre
    cL
    zre
    cJ
    cK
    cL
    letr
    syl3an
end
