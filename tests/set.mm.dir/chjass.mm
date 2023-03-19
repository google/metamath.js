include "cch.mm"
include "wcel.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "chil.mm"
include "cif.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "ifchhv.mm"
include "chjassi.mm"
include "dedth3h.mm"

theorem chjass
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CH /\ B e. CH /\ C e. CH ) -> ( ( A vH B ) vH C ) = ( A vH ( B vH C ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    cC
    cch
    wcel
    #
    cA
    cB
    chj
    co
    #
    cC
    chj
    co
    #
    cA
    cB
    cC
    chj
    co
    #
    chj
    co
    #
    wceq
    @0
    cA
    chil
    cif
    #
    cB
    chj
    co
    #
    cC
    chj
    co
    #
    @7
    @5
    chj
    co
    #
    wceq
    @7
    @1
    cB
    chil
    cif
    #
    chj
    co
    #
    cC
    chj
    co
    #
    @7
    @11
    cC
    chj
    co
    #
    chj
    co
    #
    wceq
    @12
    @2
    cC
    chil
    cif
    #
    chj
    co
    #
    @7
    @11
    @16
    chj
    co
    #
    chj
    co
    #
    wceq
    cA
    cB
    cC
    chil
    chil
    chil
    cA
    @7
    wceq
    #
    @4
    @9
    @6
    @10
    @20
    @3
    @8
    cC
    chj
    cA
    @7
    cB
    chj
    oveq1
    oveq1d
    cA
    @7
    @5
    chj
    oveq1
    eqeq12d
    cB
    @11
    wceq
    #
    @9
    @13
    @10
    @15
    @21
    @8
    @12
    cC
    chj
    cB
    @11
    @7
    chj
    oveq2
    oveq1d
    @21
    @5
    @14
    @7
    chj
    cB
    @11
    cC
    chj
    oveq1
    oveq2d
    eqeq12d
    cC
    @16
    wceq
    #
    @13
    @17
    @15
    @19
    cC
    @16
    @12
    chj
    oveq2
    @22
    @14
    @18
    @7
    chj
    cC
    @16
    @11
    chj
    oveq2
    oveq2d
    eqeq12d
    @7
    @11
    @16
    cA
    ifchhv
    cB
    ifchhv
    cC
    ifchhv
    chjassi
    dedth3h
end
