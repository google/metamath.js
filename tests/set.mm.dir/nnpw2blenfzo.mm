include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cblen.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cexp.mm"
include "cfzo.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wa.mm"
include "nnpw2blen.mm"
include "cz.mm"
include "wb.mm"
include "nnz.mm"
include "cn0.mm"
include "2z.mm"
include "blennnelnn.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "zexpcl.mm"
include "sylancr.mm"
include "nnnn0d.mm"
include "elfzo.mm"
include "syl3anc.mm"
include "mpbird.mm"

theorem nnpw2blenfzo
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. NN -> N e. ( ( 2 ^ ( ( #b ` N ) - 1 ) ) ..^ ( 2 ^ ( #b ` N ) ) ) )

  proof
    cN
    cn
    wcel
    #
    cN
    c2
    cN
    cblen
    cfv
    #
    c1
    cmin
    co
    #
    cexp
    co
    #
    c2
    @1
    cexp
    co
    #
    cfzo
    co
    wcel
    #
    @3
    cN
    cle
    wbr
    cN
    @4
    clt
    wbr
    wa
    #
    cN
    nnpw2blen
    @0
    cN
    cz
    wcel
    @3
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    @5
    @6
    wb
    cN
    nnz
    @0
    c2
    cz
    wcel
    #
    @2
    cn0
    wcel
    #
    @7
    2z
    @0
    @1
    cn
    wcel
    @10
    cN
    blennnelnn
    #
    @1
    nnm1nn0
    syl
    c2
    @2
    zexpcl
    sylancr
    @0
    @9
    @1
    cn0
    wcel
    @8
    2z
    @0
    @1
    @11
    nnnn0d
    c2
    @1
    zexpcl
    sylancr
    cN
    @3
    @4
    elfzo
    syl3anc
    mpbird
end
