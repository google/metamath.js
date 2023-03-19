include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "wa.mm"
include "cun.mm"
include "csuc.mm"
include "unexb.mm"
include "snex.mm"
include "biantru.mm"
include "df-suc.mm"
include "eleq1i.mm"
include "3bitr4i.mm"

theorem sucexb
  let cA: class A


  assert |- ( A e. _V <-> suc A e. _V )

  proof
    cA
    cvv
    wcel
    #
    cA
    csn
    #
    cvv
    wcel
    #
    wa
    cA
    @1
    cun
    #
    cvv
    wcel
    @0
    cA
    csuc
    #
    cvv
    wcel
    cA
    @1
    unexb
    @2
    @0
    cA
    snex
    biantru
    @4
    @3
    cvv
    cA
    df-suc
    eleq1i
    3bitr4i
end
