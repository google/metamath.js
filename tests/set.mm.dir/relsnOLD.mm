include "csn.mm"
include "wrel.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "wcel.mm"
include "df-rel.mm"
include "snss.mm"
include "bitr4i.mm"

theorem relsnOLD
  let cA: class A
  assume relsn.1: |- A e. _V


  assert |- ( Rel { A } <-> A e. ( _V X. _V ) )

  proof
    cA
    csn
    #
    wrel
    @0
    cvv
    cvv
    cxp
    #
    wss
    cA
    @1
    wcel
    @0
    df-rel
    cA
    @1
    relsn.1
    snss
    bitr4i
end
