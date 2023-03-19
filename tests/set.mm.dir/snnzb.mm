include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "c0.mm"
include "wne.mm"
include "wn.mm"
include "wceq.mm"
include "snprc.mm"
include "df-ne.mm"
include "con2bii.mm"
include "bitri.mm"
include "con4bii.mm"

theorem snnzb
  let cA: class A


  assert |- ( A e. _V <-> { A } =/= (/) )

  proof
    cA
    cvv
    wcel
    #
    cA
    csn
    #
    c0
    wne
    #
    @0
    wn
    @1
    c0
    wceq
    #
    @2
    wn
    cA
    snprc
    @2
    @3
    @1
    c0
    df-ne
    con2bii
    bitri
    con4bii
end
