include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "elfzuz3.mm"
include "eluzle.mm"
include "syl.mm"

theorem elfzle2
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ... N ) -> K <_ N )

  proof
    cK
    cM
    cN
    cfz
    co
    wcel
    cN
    cK
    cuz
    cfv
    wcel
    cK
    cN
    cle
    wbr
    cK
    cM
    cN
    elfzuz3
    cK
    cN
    eluzle
    syl
end
