include "chil.mm"
include "wcel.mm"
include "c0v.mm"
include "wne.mm"
include "csn.mm"
include "cort.mm"
include "cfv.mm"
include "c0h.mm"
include "wceq.mm"
include "h1did.mm"
include "eleq2.mm"
include "syl5ibcom.mm"
include "elch0.mm"
include "syl6ib.mm"
include "necon3d.mm"
include "imp.mm"

theorem h1dn0
  let cA: class A


  assert |- ( ( A e. ~H /\ A =/= 0h ) -> ( _|_ ` ( _|_ ` { A } ) ) =/= 0H )

  proof
    cA
    chil
    wcel
    #
    cA
    c0v
    wne
    cA
    csn
    cort
    cfv
    cort
    cfv
    #
    c0h
    wne
    @0
    @1
    c0h
    cA
    c0v
    @0
    @1
    c0h
    wceq
    #
    cA
    c0h
    wcel
    #
    cA
    c0v
    wceq
    @0
    cA
    @1
    wcel
    @2
    @3
    cA
    h1did
    @1
    c0h
    cA
    eleq2
    syl5ibcom
    cA
    elch0
    syl6ib
    necon3d
    imp
end
