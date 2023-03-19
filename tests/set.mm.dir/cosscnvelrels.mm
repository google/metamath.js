include "wcel.mm"
include "ccnv.mm"
include "crels.mm"
include "ccoss.mm"
include "cnvelrels.mm"
include "cosselrels.mm"
include "syl.mm"

theorem cosscnvelrels
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ,~ `' A e. Rels )

  proof
    cA
    cV
    wcel
    cA
    ccnv
    #
    crels
    wcel
    @0
    ccoss
    crels
    wcel
    cA
    cV
    cnvelrels
    @0
    crels
    cosselrels
    syl
end
