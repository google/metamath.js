include "wlim.mm"
include "csuc.mm"
include "ccmp.mm"
include "wcel.mm"
include "wn.mm"
include "con0.mm"
include "cif.mm"
include "wceq.mm"
include "suceq.mm"
include "eleq1d.mm"
include "notbid.mm"
include "limeq.mm"
include "limon.mm"
include "elimhyp.mm"
include "limsucncmpi.mm"
include "dedth.mm"

theorem limsucncmp
  let cA: class A


  assert |- ( Lim A -> -. suc A e. Comp )

  proof
    cA
    wlim
    #
    cA
    csuc
    #
    ccmp
    wcel
    #
    wn
    @0
    cA
    con0
    cif
    #
    csuc
    #
    ccmp
    wcel
    #
    wn
    cA
    con0
    cA
    @3
    wceq
    #
    @2
    @5
    @6
    @1
    @4
    ccmp
    cA
    @3
    suceq
    eleq1d
    notbid
    @3
    @0
    @3
    wlim
    con0
    wlim
    cA
    con0
    cA
    @3
    limeq
    con0
    @3
    limeq
    limon
    elimhyp
    limsucncmpi
    dedth
end
