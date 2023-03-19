include "cch.mm"
include "wcel.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "wceq.mm"
include "wi.mm"
include "chil.mm"
include "cif.mm"
include "sseq2.mm"
include "id.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "ineq12d.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "sseq1.mm"
include "oveq2.mm"
include "ineq2d.mm"
include "eqeq12d.mm"
include "ifchhv.mm"
include "pjoml3i.mm"
include "dedth2h.mm"

theorem pjoml3
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( B C_ A -> ( A i^i ( ( _|_ ` A ) vH B ) ) = B ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    cB
    cA
    wss
    #
    cA
    cA
    cort
    cfv
    #
    cB
    chj
    co
    #
    cin
    #
    cB
    wceq
    #
    wi
    cB
    @0
    cA
    chil
    cif
    #
    wss
    #
    @7
    @7
    cort
    cfv
    #
    cB
    chj
    co
    #
    cin
    #
    cB
    wceq
    #
    wi
    @1
    cB
    chil
    cif
    #
    @7
    wss
    #
    @7
    @9
    @13
    chj
    co
    #
    cin
    #
    @13
    wceq
    #
    wi
    cA
    cB
    chil
    chil
    cA
    @7
    wceq
    #
    @2
    @8
    @6
    @12
    cA
    @7
    cB
    sseq2
    @18
    @5
    @11
    cB
    @18
    cA
    @7
    @4
    @10
    @18
    id
    @18
    @3
    @9
    cB
    chj
    cA
    @7
    cort
    fveq2
    oveq1d
    ineq12d
    eqeq1d
    imbi12d
    cB
    @13
    wceq
    #
    @8
    @14
    @12
    @17
    cB
    @13
    @7
    sseq1
    @19
    @11
    @16
    cB
    @13
    @19
    @10
    @15
    @7
    cB
    @13
    @9
    chj
    oveq2
    ineq2d
    @19
    id
    eqeq12d
    imbi12d
    @7
    @13
    cA
    ifchhv
    cB
    ifchhv
    pjoml3i
    dedth2h
end
