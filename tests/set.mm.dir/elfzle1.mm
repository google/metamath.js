include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "elfzuz.mm"
include "eluzle.mm"
include "syl.mm"

theorem elfzle1
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ... N ) -> M <_ K )

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
    cK
    cle
    wbr
    cK
    cM
    cN
    elfzuz
    cM
    cK
    eluzle
    syl
end
