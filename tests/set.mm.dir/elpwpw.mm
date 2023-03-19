include "cpw.mm"
include "wcel.mm"
include "cvv.mm"
include "wss.mm"
include "wa.mm"
include "cuni.mm"
include "elpwb.mm"
include "sspwuni.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem elpwpw
  let cA: class A
  let cB: class B


  assert |- ( A e. ~P ~P B <-> ( A e. _V /\ U. A C_ B ) )

  proof
    cA
    cB
    cpw
    #
    cpw
    wcel
    cA
    cvv
    wcel
    #
    cA
    @0
    wss
    #
    wa
    @1
    cA
    cuni
    cB
    wss
    #
    wa
    cA
    @0
    elpwb
    @2
    @3
    @1
    cA
    cB
    sspwuni
    anbi2i
    bitri
end
