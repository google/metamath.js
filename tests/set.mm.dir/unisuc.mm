include "cuni.mm"
include "wss.mm"
include "cun.mm"
include "wceq.mm"
include "wtr.mm"
include "csuc.mm"
include "ssequn1.mm"
include "df-tr.mm"
include "csn.mm"
include "df-suc.mm"
include "unieqi.mm"
include "uniun.mm"
include "unisn.mm"
include "uneq2i.mm"
include "3eqtri.mm"
include "eqeq1i.mm"
include "3bitr4i.mm"

theorem unisuc
  let cA: class A
  assume unisuc.1: |- A e. _V


  assert |- ( Tr A <-> U. suc A = A )

  proof
    cA
    cuni
    #
    cA
    wss
    @0
    cA
    cun
    #
    cA
    wceq
    cA
    wtr
    cA
    csuc
    #
    cuni
    #
    cA
    wceq
    @0
    cA
    ssequn1
    cA
    df-tr
    @3
    @1
    cA
    @3
    cA
    cA
    csn
    #
    cun
    #
    cuni
    @0
    @4
    cuni
    #
    cun
    @1
    @2
    @5
    cA
    df-suc
    unieqi
    cA
    @4
    uniun
    @6
    cA
    @0
    cA
    unisuc.1
    unisn
    uneq2i
    3eqtri
    eqeq1i
    3bitr4i
end
