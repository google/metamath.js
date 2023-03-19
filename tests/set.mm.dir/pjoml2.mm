include "cch.mm"
include "wcel.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "cin.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "c0h.mm"
include "cif.mm"
include "sseq1.mm"
include "id.mm"
include "fveq2.mm"
include "ineq1d.mm"
include "oveq12d.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "sseq2.mm"
include "ineq2.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "h0elch.mm"
include "elimel.mm"
include "pjoml2i.mm"
include "dedth2h.mm"
include "3impia.mm"

theorem pjoml2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH /\ A C_ B ) -> ( A vH ( ( _|_ ` A ) i^i B ) ) = B )

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
    wss
    #
    cA
    cA
    cort
    cfv
    #
    cB
    cin
    #
    chj
    co
    #
    cB
    wceq
    #
    @0
    @1
    @2
    @6
    wi
    @0
    cA
    c0h
    cif
    #
    cB
    wss
    #
    @7
    @7
    cort
    cfv
    #
    cB
    cin
    #
    chj
    co
    #
    cB
    wceq
    #
    wi
    @7
    @1
    cB
    c0h
    cif
    #
    wss
    #
    @7
    @9
    @13
    cin
    #
    chj
    co
    #
    @13
    wceq
    #
    wi
    cA
    cB
    c0h
    c0h
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
    sseq1
    @18
    @5
    @11
    cB
    @18
    cA
    @7
    @4
    @10
    chj
    @18
    id
    @18
    @3
    @9
    cB
    cA
    @7
    cort
    fveq2
    ineq1d
    oveq12d
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
    sseq2
    @19
    @11
    @16
    cB
    @13
    @19
    @10
    @15
    @7
    chj
    cB
    @13
    @9
    ineq2
    oveq2d
    @19
    id
    eqeq12d
    imbi12d
    @7
    @13
    cA
    c0h
    cch
    h0elch
    elimel
    cB
    c0h
    cch
    h0elch
    elimel
    pjoml2i
    dedth2h
    3impia
end
