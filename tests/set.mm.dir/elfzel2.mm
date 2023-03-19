include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "elfzuz3.mm"
include "eluzelz.mm"
include "syl.mm"

theorem elfzel2
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ... N ) -> N e. ZZ )

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
    cN
    cz
    wcel
    cK
    cM
    cN
    elfzuz3
    cK
    cN
    eluzelz
    syl
end
