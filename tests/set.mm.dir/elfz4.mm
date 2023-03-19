include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "elfz2.mm"
include "biimpri.mm"

theorem elfz4
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( ( M e. ZZ /\ N e. ZZ /\ K e. ZZ ) /\ ( M <_ K /\ K <_ N ) ) -> K e. ( M ... N ) )

  proof
    cK
    cM
    cN
    cfz
    co
    wcel
    cM
    cz
    wcel
    cN
    cz
    wcel
    cK
    cz
    wcel
    w3a
    cM
    cK
    cle
    wbr
    cK
    cN
    cle
    wbr
    wa
    wa
    cK
    cM
    cN
    elfz2
    biimpri
end
