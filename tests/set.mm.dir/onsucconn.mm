include "con0.mm"
include "wcel.mm"
include "csuc.mm"
include "cconn.mm"
include "c0.mm"
include "cif.mm"
include "wceq.mm"
include "suceq.mm"
include "eleq1d.mm"
include "0elon.mm"
include "elimel.mm"
include "onsucconni.mm"
include "dedth.mm"

theorem onsucconn
  let cA: class A


  assert |- ( A e. On -> suc A e. Conn )

  proof
    cA
    con0
    wcel
    #
    cA
    csuc
    #
    cconn
    wcel
    @0
    cA
    c0
    cif
    #
    csuc
    #
    cconn
    wcel
    cA
    c0
    cA
    @2
    wceq
    @1
    @3
    cconn
    cA
    @2
    suceq
    eleq1d
    @2
    cA
    c0
    con0
    0elon
    elimel
    onsucconni
    dedth
end
