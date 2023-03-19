include "wnel.mm"
include "csn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cxp.mm"
include "cima.mm"
include "wcel.mm"
include "wn.mm"
include "disjsn.mm"
include "df-nel.mm"
include "bitr4i.mm"
include "xpima1.mm"
include "sylbir.mm"

theorem bj-xpima1snALT
  let cA: class A
  let cB: class B
  let cX: class X


  assert |- ( X e/ A -> ( ( A X. B ) " { X } ) = (/) )

  proof
    cX
    cA
    wnel
    #
    cA
    cX
    csn
    #
    cin
    c0
    wceq
    #
    cA
    cB
    cxp
    @1
    cima
    c0
    wceq
    @2
    cX
    cA
    wcel
    wn
    @0
    cA
    cX
    disjsn
    cX
    cA
    df-nel
    bitr4i
    cA
    cB
    @1
    xpima1
    sylbir
end
