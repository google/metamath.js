include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "subid.mm"
include "adantl.mm"
include "eqeq2d.mm"
include "wb.mm"
include "subcan2.mm"
include "3anidm23.mm"
include "bitr3d.mm"

theorem subeq0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( A - B ) = 0 <-> A = B ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    cB
    cmin
    co
    #
    cB
    cB
    cmin
    co
    #
    wceq
    #
    @3
    cc0
    wceq
    cA
    cB
    wceq
    #
    @2
    @4
    cc0
    @3
    @1
    @4
    cc0
    wceq
    @0
    cB
    subid
    adantl
    eqeq2d
    @0
    @1
    @5
    @6
    wb
    cA
    cB
    cB
    subcan2
    3anidm23
    bitr3d
end
