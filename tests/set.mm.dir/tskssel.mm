include "ctsk.mm"
include "wcel.mm"
include "wss.mm"
include "csdm.mm"
include "wbr.mm"
include "w3a.mm"
include "cen.mm"
include "wn.mm"
include "sdomnen.mm"
include "3ad2ant3.mm"
include "wo.mm"
include "tsken.mm"
include "3adant3.mm"
include "ord.mm"
include "mpd.mm"

theorem tskssel
  let cA: class A
  let cT: class T


  assert |- ( ( T e. Tarski /\ A C_ T /\ A ~< T ) -> A e. T )

  proof
    cT
    ctsk
    wcel
    #
    cA
    cT
    wss
    #
    cA
    cT
    csdm
    wbr
    #
    w3a
    #
    cA
    cT
    cen
    wbr
    #
    wn
    #
    cA
    cT
    wcel
    #
    @2
    @0
    @5
    @1
    cA
    cT
    sdomnen
    3ad2ant3
    @3
    @4
    @6
    @0
    @1
    @4
    @6
    wo
    @2
    cA
    cT
    tsken
    3adant3
    ord
    mpd
end
