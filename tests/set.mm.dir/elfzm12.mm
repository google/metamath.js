include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cz.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "nnz.mm"
include "cle.mm"
include "wbr.mm"
include "zre.mm"
include "lem1d.mm"
include "wb.mm"
include "peano2zm.mm"
include "eluz.mm"
include "mpancom.mm"
include "mpbird.mm"
include "fzss2.mm"
include "3syl.mm"
include "sseld.mm"

theorem elfzm12
  let cM: class M
  let cN: class N


  assert |- ( N e. NN -> ( M e. ( 1 ... ( N - 1 ) ) -> M e. ( 1 ... N ) ) )

  proof
    cN
    cn
    wcel
    #
    c1
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    c1
    cN
    cfz
    co
    #
    cM
    @0
    cN
    cz
    wcel
    #
    cN
    @1
    cuz
    cfv
    wcel
    #
    @2
    @3
    wss
    cN
    nnz
    @4
    @5
    @1
    cN
    cle
    wbr
    #
    @4
    cN
    cN
    zre
    lem1d
    @1
    cz
    wcel
    @4
    @5
    @6
    wb
    cN
    peano2zm
    @1
    cN
    eluz
    mpancom
    mpbird
    @1
    c1
    cN
    fzss2
    3syl
    sseld
end
