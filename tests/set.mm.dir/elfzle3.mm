include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "elfzuz2.mm"
include "eluzle.mm"
include "syl.mm"

theorem elfzle3
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ... N ) -> M <_ N )

  proof
    cK
    cM
    cN
    cfz
    co
    wcel
    cN
    cM
    cuz
    cfv
    wcel
    cM
    cN
    cle
    wbr
    cK
    cM
    cN
    elfzuz2
    cM
    cN
    eluzle
    syl
end
