include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "wne.mm"
include "wa.mm"
include "cn0.mm"
include "cc0.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "nnnn0.mm"
include "adantr.mm"
include "nnne0.mm"
include "simpr.mm"
include "nn0n0n1ge2.mm"
include "syl3anc.mm"

theorem nnne1ge2
  let cN: class N


  assert |- ( ( N e. NN /\ N =/= 1 ) -> 2 <_ N )

  proof
    cN
    cn
    wcel
    #
    cN
    c1
    wne
    #
    wa
    cN
    cn0
    wcel
    #
    cN
    cc0
    wne
    #
    @1
    c2
    cN
    cle
    wbr
    @0
    @2
    @1
    cN
    nnnn0
    adantr
    @0
    @3
    @1
    cN
    nnne0
    adantr
    @0
    @1
    simpr
    cN
    nn0n0n1ge2
    syl3anc
end
