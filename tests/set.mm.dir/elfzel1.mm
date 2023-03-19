include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "elfzuz.mm"
include "eluzel2.mm"
include "syl.mm"

theorem elfzel1
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ... N ) -> M e. ZZ )

  proof
    cK
    cM
    cN
    cfz
    co
    wcel
    cK
    cM
    cuz
    cfv
    wcel
    cM
    cz
    wcel
    cK
    cM
    cN
    elfzuz
    cM
    cK
    eluzel2
    syl
end
