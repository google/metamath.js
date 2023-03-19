include "cch.mm"
include "wcel.mm"
include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "cph.mm"
include "co.mm"
include "chj.mm"
include "wceq.mm"
include "wi.mm"
include "chil.mm"
include "cif.mm"
include "sseq1.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "oveq2.mm"
include "ifchhv.mm"
include "osumi.mm"
include "dedth2h.mm"
include "3impia.mm"

theorem osum
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH /\ A C_ ( _|_ ` B ) ) -> ( A +H B ) = ( A vH B ) )

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
    cort
    cfv
    #
    wss
    #
    cA
    cB
    cph
    co
    #
    cA
    cB
    chj
    co
    #
    wceq
    #
    @0
    @1
    @3
    @6
    wi
    @0
    cA
    chil
    cif
    #
    @2
    wss
    #
    @7
    cB
    cph
    co
    #
    @7
    cB
    chj
    co
    #
    wceq
    #
    wi
    @7
    @1
    cB
    chil
    cif
    #
    cort
    cfv
    #
    wss
    #
    @7
    @12
    cph
    co
    #
    @7
    @12
    chj
    co
    #
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
    @3
    @8
    @6
    @11
    cA
    @7
    @2
    sseq1
    @18
    @4
    @9
    @5
    @10
    cA
    @7
    cB
    cph
    oveq1
    cA
    @7
    cB
    chj
    oveq1
    eqeq12d
    imbi12d
    cB
    @12
    wceq
    #
    @8
    @14
    @11
    @17
    @19
    @2
    @13
    @7
    cB
    @12
    cort
    fveq2
    sseq2d
    @19
    @9
    @15
    @10
    @16
    cB
    @12
    @7
    cph
    oveq2
    cB
    @12
    @7
    chj
    oveq2
    eqeq12d
    imbi12d
    @7
    @12
    cA
    ifchhv
    cB
    ifchhv
    osumi
    dedth2h
    3impia
end
