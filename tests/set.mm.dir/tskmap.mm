include "ctsk.mm"
include "wcel.mm"
include "wtr.mm"
include "wa.mm"
include "w3a.mm"
include "cwun.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "tskwun.mm"
include "3expa.mm"
include "sylan2.mm"
include "3adant3.mm"
include "simp2.mm"
include "simp3.mm"
include "wunmap.mm"

theorem tskmap
  let cA: class A
  let cB: class B
  let cT: class T


  assert |- ( ( ( T e. Tarski /\ Tr T ) /\ A e. T /\ B e. T ) -> ( A ^m B ) e. T )

  proof
    cT
    ctsk
    wcel
    #
    cT
    wtr
    #
    wa
    #
    cA
    cT
    wcel
    #
    cB
    cT
    wcel
    #
    w3a
    cA
    cB
    cT
    @2
    @3
    cT
    cwun
    wcel
    #
    @4
    @3
    @2
    cT
    c0
    wne
    #
    @5
    cT
    cA
    ne0i
    @0
    @1
    @6
    @5
    cT
    tskwun
    3expa
    sylan2
    3adant3
    @2
    @3
    @4
    simp2
    @2
    @3
    @4
    simp3
    wunmap
end
