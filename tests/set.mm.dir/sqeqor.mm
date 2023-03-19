include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cneg.mm"
include "wo.mm"
include "wb.mm"
include "cc0.mm"
include "cif.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "orbi12d.mm"
include "bibi12d.mm"
include "eqeq2d.mm"
include "eqeq2.mm"
include "negeq.mm"
include "0cn.mm"
include "elimel.mm"
include "sqeqori.mm"
include "dedth2h.mm"

theorem sqeqor
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( A ^ 2 ) = ( B ^ 2 ) <-> ( A = B \/ A = -u B ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    wceq
    #
    cA
    cB
    wceq
    #
    cA
    cB
    cneg
    #
    wceq
    #
    wo
    #
    wb
    @0
    cA
    cc0
    cif
    #
    c2
    cexp
    co
    #
    @3
    wceq
    #
    @9
    cB
    wceq
    #
    @9
    @6
    wceq
    #
    wo
    #
    wb
    @10
    @1
    cB
    cc0
    cif
    #
    c2
    cexp
    co
    #
    wceq
    #
    @9
    @15
    wceq
    #
    @9
    @15
    cneg
    #
    wceq
    #
    wo
    #
    wb
    cA
    cB
    cc0
    cc0
    cA
    @9
    wceq
    #
    @4
    @11
    @8
    @14
    @22
    @2
    @10
    @3
    cA
    @9
    c2
    cexp
    oveq1
    eqeq1d
    @22
    @5
    @12
    @7
    @13
    cA
    @9
    cB
    eqeq1
    cA
    @9
    @6
    eqeq1
    orbi12d
    bibi12d
    cB
    @15
    wceq
    #
    @11
    @17
    @14
    @21
    @23
    @3
    @16
    @10
    cB
    @15
    c2
    cexp
    oveq1
    eqeq2d
    @23
    @12
    @18
    @13
    @20
    cB
    @15
    @9
    eqeq2
    @23
    @6
    @19
    @9
    cB
    @15
    negeq
    eqeq2d
    orbi12d
    bibi12d
    @9
    @15
    cA
    cc0
    cc
    0cn
    elimel
    cB
    cc0
    cc
    0cn
    elimel
    sqeqori
    dedth2h
end
