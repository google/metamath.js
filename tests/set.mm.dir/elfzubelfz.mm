include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "elfzuz2.mm"
include "eluzfz2.mm"
include "syl.mm"

theorem elfzubelfz
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ... N ) -> N e. ( M ... N ) )

  proof
    cK
    cM
    cN
    cfz
    co
    #
    wcel
    cN
    cM
    cuz
    cfv
    wcel
    cN
    @0
    wcel
    cK
    cM
    cN
    elfzuz2
    cM
    cN
    eluzfz2
    syl
end
