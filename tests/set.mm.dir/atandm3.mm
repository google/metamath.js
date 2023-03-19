include "cc.mm"
include "wcel.mm"
include "ci.mm"
include "cneg.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "catan.mm"
include "cdm.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "3anass.mm"
include "atandm.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "wb.mm"
include "ax-icn.mm"
include "sqeqor.mm"
include "mpan2.mm"
include "i2.mm"
include "eqeq2i.mm"
include "orcom.mm"
include "3bitr3g.mm"
include "necon3abid.mm"
include "neanior.mm"
include "syl6bbr.mm"
include "pm5.32i.mm"
include "3bitr4i.mm"

theorem atandm3
  let cA: class A


  assert |- ( A e. dom arctan <-> ( A e. CC /\ ( A ^ 2 ) =/= -u 1 ) )

  proof
    cA
    cc
    wcel
    #
    cA
    ci
    cneg
    #
    wne
    #
    cA
    ci
    wne
    #
    w3a
    @0
    @2
    @3
    wa
    #
    wa
    cA
    catan
    cdm
    wcel
    @0
    cA
    c2
    cexp
    co
    #
    c1
    cneg
    #
    wne
    #
    wa
    @0
    @2
    @3
    3anass
    cA
    atandm
    @0
    @7
    @4
    @0
    @7
    cA
    @1
    wceq
    #
    cA
    ci
    wceq
    #
    wo
    #
    wn
    @4
    @0
    @10
    @5
    @6
    @0
    @5
    ci
    c2
    cexp
    co
    #
    wceq
    #
    @9
    @8
    wo
    #
    @5
    @6
    wceq
    @10
    @0
    ci
    cc
    wcel
    @12
    @13
    wb
    ax-icn
    cA
    ci
    sqeqor
    mpan2
    @11
    @6
    @5
    i2
    eqeq2i
    @9
    @8
    orcom
    3bitr3g
    necon3abid
    cA
    @1
    cA
    ci
    neanior
    syl6bbr
    pm5.32i
    3bitr4i
end
