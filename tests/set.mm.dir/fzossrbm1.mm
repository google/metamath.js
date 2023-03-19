include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "cc0.mm"
include "cfzo.mm"
include "wss.mm"
include "cle.mm"
include "wbr.mm"
include "peano2zm.mm"
include "id.mm"
include "zre.mm"
include "lem1d.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "fzoss2.mm"
include "syl.mm"

theorem fzossrbm1
  let cN: class N


  assert |- ( N e. ZZ -> ( 0 ..^ ( N - 1 ) ) C_ ( 0 ..^ N ) )

  proof
    cN
    cz
    wcel
    #
    cN
    cN
    c1
    cmin
    co
    #
    cuz
    cfv
    wcel
    #
    cc0
    @1
    cfzo
    co
    cc0
    cN
    cfzo
    co
    wss
    @0
    @1
    cz
    wcel
    @0
    @1
    cN
    cle
    wbr
    @2
    cN
    peano2zm
    @0
    id
    @0
    cN
    cN
    zre
    lem1d
    @1
    cN
    eluz2
    syl3anbrc
    @1
    cc0
    cN
    fzoss2
    syl
end
