include "wcel.mm"
include "cvv.mm"
include "cxp.mm"
include "csn.mm"
include "wss.mm"
include "wrel.mm"
include "snssg.mm"
include "df-rel.mm"
include "syl6rbbr.mm"

theorem relsng
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ( Rel { A } <-> A e. ( _V X. _V ) ) )

  proof
    cA
    cV
    wcel
    cA
    cvv
    cvv
    cxp
    #
    wcel
    cA
    csn
    #
    @0
    wss
    @1
    wrel
    cA
    @0
    cV
    snssg
    @1
    df-rel
    syl6rbbr
end
