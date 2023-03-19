include "wfn.mm"
include "wrel.mm"
include "cdm.mm"
include "wss.mm"
include "cres.mm"
include "wceq.mm"
include "fnrel.mm"
include "fndm.mm"
include "eqimss.mm"
include "syl.mm"
include "relssres.mm"
include "syl2anc.mm"

theorem fnresdm
  let cA: class A
  let cF: class F


  assert |- ( F Fn A -> ( F |` A ) = F )

  proof
    cF
    cA
    wfn
    #
    cF
    wrel
    cF
    cdm
    #
    cA
    wss
    #
    cF
    cA
    cres
    cF
    wceq
    cA
    cF
    fnrel
    @0
    @1
    cA
    wceq
    @2
    cA
    cF
    fndm
    @1
    cA
    eqimss
    syl
    cF
    cA
    relssres
    syl2anc
end
