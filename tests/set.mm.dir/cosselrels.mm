include "wcel.mm"
include "ccoss.mm"
include "cvv.mm"
include "crels.mm"
include "cossex.mm"
include "wrel.mm"
include "relcoss.mm"
include "elrelsrel.mm"
include "mpbiri.mm"
include "syl.mm"

theorem cosselrels
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ,~ A e. Rels )

  proof
    cA
    cV
    wcel
    cA
    ccoss
    #
    cvv
    wcel
    #
    @0
    crels
    wcel
    #
    cA
    cV
    cossex
    @1
    @2
    @0
    wrel
    cA
    relcoss
    @0
    cvv
    elrelsrel
    mpbiri
    syl
end
