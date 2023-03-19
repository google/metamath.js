include "cch.mm"
include "wcel.mm"
include "csh.mm"
include "wa.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "cin.mm"
include "c0h.mm"
include "wceq.mm"
include "wi.mm"
include "cif.mm"
include "sseq1.mm"
include "fveq2.mm"
include "ineq2d.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "sseq2.mm"
include "ineq1.mm"
include "eqeq2.mm"
include "h0elch.mm"
include "elimel.mm"
include "h0elsh.mm"
include "pjomli.mm"
include "dedth2h.mm"
include "imp.mm"

theorem pjoml
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. CH /\ B e. SH ) /\ ( A C_ B /\ ( B i^i ( _|_ ` A ) ) = 0H ) ) -> A = B )

  proof
    cA
    cch
    wcel
    #
    cB
    csh
    wcel
    #
    wa
    cA
    cB
    wss
    #
    cB
    cA
    cort
    cfv
    #
    cin
    #
    c0h
    wceq
    #
    wa
    #
    cA
    cB
    wceq
    #
    @0
    @1
    @6
    @7
    wi
    @0
    cA
    c0h
    cif
    #
    cB
    wss
    #
    cB
    @8
    cort
    cfv
    #
    cin
    #
    c0h
    wceq
    #
    wa
    #
    @8
    cB
    wceq
    #
    wi
    @8
    @1
    cB
    c0h
    cif
    #
    wss
    #
    @15
    @10
    cin
    #
    c0h
    wceq
    #
    wa
    #
    @8
    @15
    wceq
    #
    wi
    cA
    cB
    c0h
    c0h
    cA
    @8
    wceq
    #
    @6
    @13
    @7
    @14
    @21
    @2
    @9
    @5
    @12
    cA
    @8
    cB
    sseq1
    @21
    @4
    @11
    c0h
    @21
    @3
    @10
    cB
    cA
    @8
    cort
    fveq2
    ineq2d
    eqeq1d
    anbi12d
    cA
    @8
    cB
    eqeq1
    imbi12d
    cB
    @15
    wceq
    #
    @13
    @19
    @14
    @20
    @22
    @9
    @16
    @12
    @18
    cB
    @15
    @8
    sseq2
    @22
    @11
    @17
    c0h
    cB
    @15
    @10
    ineq1
    eqeq1d
    anbi12d
    cB
    @15
    @8
    eqeq2
    imbi12d
    @8
    @15
    cA
    c0h
    cch
    h0elch
    elimel
    cB
    c0h
    csh
    h0elsh
    elimel
    pjomli
    dedth2h
    imp
end
