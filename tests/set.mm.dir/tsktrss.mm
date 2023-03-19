include "ctsk.mm"
include "wcel.mm"
include "wtr.mm"
include "w3a.mm"
include "cpw.mm"
include "wss.mm"
include "simp2.mm"
include "dftr4.mm"
include "sylib.mm"
include "tskpwss.mm"
include "3adant2.mm"
include "sstrd.mm"

theorem tsktrss
  let cA: class A
  let cT: class T


  assert |- ( ( T e. Tarski /\ Tr A /\ A e. T ) -> A C_ T )

  proof
    cT
    ctsk
    wcel
    #
    cA
    wtr
    #
    cA
    cT
    wcel
    #
    w3a
    #
    cA
    cA
    cpw
    #
    cT
    @3
    @1
    cA
    @4
    wss
    @0
    @1
    @2
    simp2
    cA
    dftr4
    sylib
    @0
    @2
    @4
    cT
    wss
    @1
    cA
    cT
    tskpwss
    3adant2
    sstrd
end
