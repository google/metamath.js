include "wlim.mm"
include "wcel.mm"
include "csuc.mm"
include "cen.mm"
include "wbr.mm"
include "wi.mm"
include "con0.mm"
include "cif.mm"
include "wceq.mm"
include "eleq1.mm"
include "id.mm"
include "suceq.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "limeq.mm"
include "limon.mm"
include "elimhyp.mm"
include "limensuci.mm"
include "dedth.mm"
include "impcom.mm"

theorem limensuc
  let cA: class A
  let cV: class V


  assert |- ( ( A e. V /\ Lim A ) -> A ~~ suc A )

  proof
    cA
    wlim
    #
    cA
    cV
    wcel
    #
    cA
    cA
    csuc
    #
    cen
    wbr
    #
    @0
    @1
    @3
    wi
    @0
    cA
    con0
    cif
    #
    cV
    wcel
    #
    @4
    @4
    csuc
    #
    cen
    wbr
    #
    wi
    cA
    con0
    cA
    @4
    wceq
    #
    @1
    @5
    @3
    @7
    cA
    @4
    cV
    eleq1
    @8
    cA
    @4
    @2
    @6
    cen
    @8
    id
    cA
    @4
    suceq
    breq12d
    imbi12d
    @4
    cV
    @0
    @4
    wlim
    con0
    wlim
    cA
    con0
    cA
    @4
    limeq
    con0
    @4
    limeq
    limon
    elimhyp
    limensuci
    dedth
    impcom
end
