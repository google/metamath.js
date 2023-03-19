include "cclwwlkn.mm"
include "co.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "cn.mm"
include "n0i.mm"
include "wn.mm"
include "cvv.mm"
include "wnel.mm"
include "wo.mm"
include "df-nel.mm"
include "biimpri.mm"
include "olcd.mm"
include "clwwlkneq0.mm"
include "syl.mm"
include "nsyl2.mm"

theorem clwwlknnn
  let cG: class G
  let cN: class N
  let cW: class W


  assert |- ( W e. ( N ClWWalksN G ) -> N e. NN )

  proof
    cW
    cN
    cG
    cclwwlkn
    co
    #
    wcel
    @0
    c0
    wceq
    #
    cN
    cn
    wcel
    #
    @0
    cW
    n0i
    @2
    wn
    #
    cG
    cvv
    wnel
    #
    cN
    cn
    wnel
    #
    wo
    @1
    @3
    @5
    @4
    @5
    @3
    cN
    cn
    df-nel
    biimpri
    olcd
    cG
    cN
    clwwlkneq0
    syl
    nsyl2
end
