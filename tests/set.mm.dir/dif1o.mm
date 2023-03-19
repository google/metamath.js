include "c1o.mm"
include "cdif.mm"
include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "wne.mm"
include "wa.mm"
include "df1o2.mm"
include "difeq2i.mm"
include "eleq2i.mm"
include "eldifsn.mm"
include "bitri.mm"

theorem dif1o
  let cA: class A
  let cB: class B


  assert |- ( A e. ( B \ 1o ) <-> ( A e. B /\ A =/= (/) ) )

  proof
    cA
    cB
    c1o
    cdif
    #
    wcel
    cA
    cB
    c0
    csn
    #
    cdif
    #
    wcel
    cA
    cB
    wcel
    cA
    c0
    wne
    wa
    @0
    @2
    cA
    c1o
    @1
    cB
    df1o2
    difeq2i
    eleq2i
    cA
    cB
    c0
    eldifsn
    bitri
end
