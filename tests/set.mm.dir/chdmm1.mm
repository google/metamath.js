include "cch.mm"
include "wcel.mm"
include "cin.mm"
include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "chil.mm"
include "cif.mm"
include "ineq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "ineq2.mm"
include "oveq2d.mm"
include "ifchhv.mm"
include "chdmm1i.mm"
include "dedth2h.mm"

theorem chdmm1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( _|_ ` ( A i^i B ) ) = ( ( _|_ ` A ) vH ( _|_ ` B ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    cA
    cB
    cin
    #
    cort
    cfv
    #
    cA
    cort
    cfv
    #
    cB
    cort
    cfv
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
    cin
    #
    cort
    cfv
    #
    @7
    cort
    cfv
    #
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
    cin
    #
    cort
    cfv
    #
    @10
    @12
    cort
    cfv
    #
    chj
    co
    #
    wceq
    cA
    cB
    chil
    chil
    cA
    @7
    wceq
    #
    @3
    @9
    @6
    @11
    @17
    @2
    @8
    cort
    cA
    @7
    cB
    ineq1
    fveq2d
    @17
    @4
    @10
    @5
    chj
    cA
    @7
    cort
    fveq2
    oveq1d
    eqeq12d
    cB
    @12
    wceq
    #
    @9
    @14
    @11
    @16
    @18
    @8
    @13
    cort
    cB
    @12
    @7
    ineq2
    fveq2d
    @18
    @5
    @15
    @10
    chj
    cB
    @12
    cort
    fveq2
    oveq2d
    eqeq12d
    @7
    @12
    cA
    ifchhv
    cB
    ifchhv
    chdmm1i
    dedth2h
end
