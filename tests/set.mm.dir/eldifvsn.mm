include "wcel.mm"
include "wne.mm"
include "cvv.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "elex.mm"
include "biantrurd.mm"
include "eldifsn.mm"
include "syl6rbbr.mm"

theorem eldifvsn
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> ( A e. ( _V \ { B } ) <-> A =/= B ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cB
    wne
    #
    cA
    cvv
    wcel
    #
    @1
    wa
    cA
    cvv
    cB
    csn
    cdif
    wcel
    @0
    @2
    @1
    cA
    cV
    elex
    biantrurd
    cA
    cvv
    cB
    eldifsn
    syl6rbbr
end
