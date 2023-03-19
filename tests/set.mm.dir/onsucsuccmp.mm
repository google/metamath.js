include "con0.mm"
include "wcel.mm"
include "csuc.mm"
include "ccmp.mm"
include "c0.mm"
include "cif.mm"
include "wceq.mm"
include "suceq.mm"
include "syl.mm"
include "eleq1d.mm"
include "0elon.mm"
include "elimel.mm"
include "onsucsuccmpi.mm"
include "dedth.mm"

theorem onsucsuccmp
  let cA: class A


  assert |- ( A e. On -> suc suc A e. Comp )

  proof
    cA
    con0
    wcel
    #
    cA
    csuc
    #
    csuc
    #
    ccmp
    wcel
    @0
    cA
    c0
    cif
    #
    csuc
    #
    csuc
    #
    ccmp
    wcel
    cA
    c0
    cA
    @3
    wceq
    #
    @2
    @5
    ccmp
    @6
    @1
    @4
    wceq
    @2
    @5
    wceq
    cA
    @3
    suceq
    @1
    @4
    suceq
    syl
    eleq1d
    @3
    cA
    c0
    con0
    0elon
    elimel
    onsucsuccmpi
    dedth
end
