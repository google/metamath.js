include "wcel.mm"
include "csn.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "cxp.mm"
include "cima.mm"
include "wceq.mm"
include "wn.mm"
include "disjsn.mm"
include "necon3abii.mm"
include "notnotb.mm"
include "bitr4i.mm"
include "xpima2.mm"
include "sylbir.mm"

theorem xpimasn
  let cA: class A
  let cB: class B
  let cX: class X


  assert |- ( X e. A -> ( ( A X. B ) " { X } ) = B )

  proof
    cX
    cA
    wcel
    #
    cA
    cX
    csn
    #
    cin
    #
    c0
    wne
    #
    cA
    cB
    cxp
    @1
    cima
    cB
    wceq
    @3
    @0
    wn
    #
    wn
    @0
    @4
    @2
    c0
    cA
    cX
    disjsn
    necon3abii
    @0
    notnotb
    bitr4i
    cA
    cB
    @1
    xpima2
    sylbir
end
