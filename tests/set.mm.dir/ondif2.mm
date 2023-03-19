include "con0.mm"
include "c2o.mm"
include "cdif.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "c1o.mm"
include "eldif.mm"
include "wb.mm"
include "1on.mm"
include "wss.mm"
include "ontri1.mm"
include "csuc.mm"
include "onsssuc.mm"
include "df-2o.mm"
include "eleq2i.mm"
include "syl6bbr.mm"
include "bitr3d.mm"
include "mpan2.mm"
include "con1bid.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem ondif2
  let cA: class A


  assert |- ( A e. ( On \ 2o ) <-> ( A e. On /\ 1o e. A ) )

  proof
    cA
    con0
    c2o
    cdif
    wcel
    cA
    con0
    wcel
    #
    cA
    c2o
    wcel
    #
    wn
    #
    wa
    @0
    c1o
    cA
    wcel
    #
    wa
    cA
    con0
    c2o
    eldif
    @0
    @2
    @3
    @0
    @3
    @1
    @0
    c1o
    con0
    wcel
    #
    @3
    wn
    #
    @1
    wb
    1on
    @0
    @4
    wa
    #
    cA
    c1o
    wss
    #
    @5
    @1
    cA
    c1o
    ontri1
    @6
    @7
    cA
    c1o
    csuc
    #
    wcel
    @1
    cA
    c1o
    onsssuc
    c2o
    @8
    cA
    df-2o
    eleq2i
    syl6bbr
    bitr3d
    mpan2
    con1bid
    pm5.32i
    bitri
end
