include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "csn.mm"
include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "wceq.mm"
include "c0h.mm"
include "wo.mm"
include "wi.mm"
include "cif.mm"
include "c0v.mm"
include "sseq1.mm"
include "eqeq1.mm"
include "orbi12d.mm"
include "imbi12d.mm"
include "sneq.mm"
include "fveq2d.mm"
include "sseq2d.mm"
include "eqeq2d.mm"
include "orbi1d.mm"
include "h0elch.mm"
include "elimel.mm"
include "ifhvhv0.mm"
include "h1datomi.mm"
include "dedth2h.mm"

theorem h1datom
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. ~H ) -> ( A C_ ( _|_ ` ( _|_ ` { B } ) ) -> ( A = ( _|_ ` ( _|_ ` { B } ) ) \/ A = 0H ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    chil
    wcel
    #
    cA
    cB
    csn
    #
    cort
    cfv
    #
    cort
    cfv
    #
    wss
    #
    cA
    @4
    wceq
    #
    cA
    c0h
    wceq
    #
    wo
    #
    wi
    @0
    cA
    c0h
    cif
    #
    @4
    wss
    #
    @9
    @4
    wceq
    #
    @9
    c0h
    wceq
    #
    wo
    #
    wi
    @9
    @1
    cB
    c0v
    cif
    #
    csn
    #
    cort
    cfv
    #
    cort
    cfv
    #
    wss
    #
    @9
    @17
    wceq
    #
    @12
    wo
    #
    wi
    cA
    cB
    c0h
    c0v
    cA
    @9
    wceq
    #
    @5
    @10
    @8
    @13
    cA
    @9
    @4
    sseq1
    @21
    @6
    @11
    @7
    @12
    cA
    @9
    @4
    eqeq1
    cA
    @9
    c0h
    eqeq1
    orbi12d
    imbi12d
    cB
    @14
    wceq
    #
    @10
    @18
    @13
    @20
    @22
    @4
    @17
    @9
    @22
    @3
    @16
    cort
    @22
    @2
    @15
    cort
    cB
    @14
    sneq
    fveq2d
    fveq2d
    #
    sseq2d
    @22
    @11
    @19
    @12
    @22
    @4
    @17
    @9
    @23
    eqeq2d
    orbi1d
    imbi12d
    @9
    @14
    cA
    c0h
    cch
    h0elch
    elimel
    cB
    ifhvhv0
    h1datomi
    dedth2h
end
