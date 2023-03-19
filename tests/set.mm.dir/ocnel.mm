include "csh.mm"
include "wcel.mm"
include "cort.mm"
include "cfv.mm"
include "c0v.mm"
include "wne.mm"
include "wn.mm"
include "wa.mm"
include "c0h.mm"
include "wceq.mm"
include "wi.mm"
include "cin.mm"
include "elin.mm"
include "ocin.mm"
include "eleq2d.mm"
include "biimpd.mm"
include "syl5bir.mm"
include "expcomd.mm"
include "imp.mm"
include "elch0.mm"
include "syl6ib.mm"
include "necon3ad.mm"
include "3impia.mm"

theorem ocnel
  let cA: class A
  let cH: class H


  assert |- ( ( H e. SH /\ A e. ( _|_ ` H ) /\ A =/= 0h ) -> -. A e. H )

  proof
    cH
    csh
    wcel
    #
    cA
    cH
    cort
    cfv
    #
    wcel
    #
    cA
    c0v
    wne
    cA
    cH
    wcel
    #
    wn
    @0
    @2
    wa
    #
    @3
    cA
    c0v
    @4
    @3
    cA
    c0h
    wcel
    #
    cA
    c0v
    wceq
    @0
    @2
    @3
    @5
    wi
    @0
    @3
    @2
    @5
    @3
    @2
    wa
    cA
    cH
    @1
    cin
    #
    wcel
    #
    @0
    @5
    cA
    cH
    @1
    elin
    @0
    @7
    @5
    @0
    @6
    c0h
    cA
    cH
    ocin
    eleq2d
    biimpd
    syl5bir
    expcomd
    imp
    cA
    elch0
    syl6ib
    necon3ad
    3impia
end
