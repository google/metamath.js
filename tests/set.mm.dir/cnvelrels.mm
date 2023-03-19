include "wcel.mm"
include "ccnv.mm"
include "crels.mm"
include "wrel.mm"
include "relcnv.mm"
include "cvv.mm"
include "wb.mm"
include "cnvexg.mm"
include "elrelsrel.mm"
include "syl.mm"
include "mpbiri.mm"

theorem cnvelrels
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> `' A e. Rels )

  proof
    cA
    cV
    wcel
    #
    cA
    ccnv
    #
    crels
    wcel
    #
    @1
    wrel
    #
    cA
    relcnv
    @0
    @1
    cvv
    wcel
    @2
    @3
    wb
    cA
    cV
    cnvexg
    @1
    cvv
    elrelsrel
    syl
    mpbiri
end
