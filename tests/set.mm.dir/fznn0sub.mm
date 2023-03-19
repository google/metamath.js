include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "cmin.mm"
include "cn0.mm"
include "elfzuz3.mm"
include "uznn0sub.mm"
include "syl.mm"

theorem fznn0sub
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ... N ) -> ( N - K ) e. NN0 )

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
    cK
    cmin
    co
    cn0
    wcel
    cK
    cM
    cN
    elfzuz3
    cK
    cN
    uznn0sub
    syl
end
