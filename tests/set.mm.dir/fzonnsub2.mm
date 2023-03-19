include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cmin.mm"
include "cn.mm"
include "elfzolt3b.mm"
include "fzonnsub.mm"
include "syl.mm"

theorem fzonnsub2
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ..^ N ) -> ( N - M ) e. NN )

  proof
    cK
    cM
    cN
    cfzo
    co
    #
    wcel
    cM
    @0
    wcel
    cN
    cM
    cmin
    co
    cn
    wcel
    cK
    cM
    cN
    elfzolt3b
    cM
    cM
    cN
    fzonnsub
    syl
end
