include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "c1.mm"
include "cun.mm"
include "csn.mm"
include "cfz.mm"
include "wceq.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "1nn0.mm"
include "a1i.mm"
include "nnnn0.mm"
include "nnge1.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "fzosplit.mm"
include "syl.mm"
include "fzo01.mm"
include "uneq1d.mm"
include "eqtrd.mm"

theorem fzo0sn0fzo1
  let cN: class N


  assert |- ( N e. NN -> ( 0 ..^ N ) = ( { 0 } u. ( 1 ..^ N ) ) )

  proof
    cN
    cn
    wcel
    #
    cc0
    cN
    cfzo
    co
    #
    cc0
    c1
    cfzo
    co
    #
    c1
    cN
    cfzo
    co
    #
    cun
    #
    cc0
    csn
    #
    @3
    cun
    @0
    c1
    cc0
    cN
    cfz
    co
    wcel
    #
    @1
    @4
    wceq
    @0
    c1
    cn0
    wcel
    #
    cN
    cn0
    wcel
    c1
    cN
    cle
    wbr
    @6
    @7
    @0
    1nn0
    a1i
    cN
    nnnn0
    cN
    nnge1
    c1
    cN
    elfz2nn0
    syl3anbrc
    cc0
    cN
    c1
    fzosplit
    syl
    @0
    @2
    @5
    @3
    @2
    @5
    wceq
    @0
    fzo01
    a1i
    uneq1d
    eqtrd
end
