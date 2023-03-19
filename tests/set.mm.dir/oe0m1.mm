include "con0.mm"
include "wcel.mm"
include "c0.mm"
include "c1o.mm"
include "wss.mm"
include "coe.mm"
include "co.mm"
include "wceq.mm"
include "word.mm"
include "wb.mm"
include "eloni.mm"
include "ordgt0ge1.mm"
include "syl.mm"
include "cdif.mm"
include "oe0m.mm"
include "eqeq1d.mm"
include "ssdif0.mm"
include "syl6rbbr.mm"
include "bitrd.mm"

theorem oe0m1
  let cA: class A


  assert |- ( A e. On -> ( (/) e. A <-> ( (/) ^o A ) = (/) ) )

  proof
    cA
    con0
    wcel
    #
    c0
    cA
    wcel
    #
    c1o
    cA
    wss
    #
    c0
    cA
    coe
    co
    #
    c0
    wceq
    #
    @0
    cA
    word
    @1
    @2
    wb
    cA
    eloni
    cA
    ordgt0ge1
    syl
    @0
    @4
    c1o
    cA
    cdif
    #
    c0
    wceq
    @2
    @0
    @3
    @5
    c0
    cA
    oe0m
    eqeq1d
    c1o
    cA
    ssdif0
    syl6rbbr
    bitrd
end
