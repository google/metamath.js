include "wcel.mm"
include "cfn.mm"
include "wn.mm"
include "chash.mm"
include "cfv.mm"
include "cn0.mm"
include "wnel.mm"
include "nnel.mm"
include "hashclb.mm"
include "biimprd.mm"
include "syl5bi.mm"
include "con1d.mm"
include "imp.mm"

theorem hashnfinnn0
  let cA: class A
  let cV: class V


  assert |- ( ( A e. V /\ -. A e. Fin ) -> ( # ` A ) e/ NN0 )

  proof
    cA
    cV
    wcel
    #
    cA
    cfn
    wcel
    #
    wn
    cA
    chash
    cfv
    #
    cn0
    wnel
    #
    @0
    @3
    @1
    @3
    wn
    @2
    cn0
    wcel
    #
    @0
    @1
    @2
    cn0
    nnel
    @0
    @1
    @4
    cA
    cV
    hashclb
    biimprd
    syl5bi
    con1d
    imp
end
