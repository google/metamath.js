include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "cin.mm"
include "c0h.mm"
include "wceq.mm"
include "wa.mm"
include "cif.mm"
include "eqeq1.mm"
include "eqeq2.mm"
include "cch.mm"
include "h0elch.mm"
include "keepel.mm"
include "csh.mm"
include "h0elsh.mm"
include "sseq1.mm"
include "fveq2.mm"
include "ineq2d.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "sseq2.mm"
include "ineq1.mm"
include "ssid.mm"
include "wcel.mm"
include "ocin.mm"
include "ax-mp.mm"
include "pm3.2i.mm"
include "elimhyp2v.mm"
include "simpli.mm"
include "simpri.mm"
include "omlsii.mm"
include "dedth2v.mm"

theorem omlsi
  let cA: class A
  let cB: class B
  assume omls.1: |- A e. CH
  assume omls.2: |- B e. SH


  assert |- ( ( A C_ B /\ ( B i^i ( _|_ ` A ) ) = 0H ) -> A = B )

  proof
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
    @4
    cA
    c0h
    cif
    #
    cB
    wceq
    @5
    @4
    cB
    c0h
    cif
    #
    wceq
    cA
    cB
    c0h
    c0h
    cA
    @5
    cB
    eqeq1
    cB
    @6
    @5
    eqeq2
    @5
    @6
    @4
    cA
    c0h
    cch
    omls.1
    h0elch
    keepel
    @4
    cB
    c0h
    csh
    omls.2
    h0elsh
    keepel
    @5
    @6
    wss
    #
    @6
    @5
    cort
    cfv
    #
    cin
    #
    c0h
    wceq
    #
    @4
    @5
    cB
    wss
    #
    cB
    @8
    cin
    #
    c0h
    wceq
    #
    wa
    @7
    @10
    wa
    c0h
    c0h
    wss
    #
    c0h
    c0h
    cort
    cfv
    #
    cin
    #
    c0h
    wceq
    #
    wa
    @5
    c0h
    wss
    #
    c0h
    @8
    cin
    #
    c0h
    wceq
    #
    wa
    cA
    cB
    c0h
    c0h
    cA
    @5
    wceq
    #
    @0
    @11
    @3
    @13
    cA
    @5
    cB
    sseq1
    @21
    @2
    @12
    c0h
    @21
    @1
    @8
    cB
    cA
    @5
    cort
    fveq2
    ineq2d
    eqeq1d
    anbi12d
    cB
    @6
    wceq
    #
    @11
    @7
    @13
    @10
    cB
    @6
    @5
    sseq2
    @22
    @12
    @9
    c0h
    cB
    @6
    @8
    ineq1
    eqeq1d
    anbi12d
    c0h
    @5
    wceq
    #
    @14
    @18
    @17
    @20
    c0h
    @5
    c0h
    sseq1
    @23
    @16
    @19
    c0h
    @23
    @15
    @8
    c0h
    c0h
    @5
    cort
    fveq2
    ineq2d
    eqeq1d
    anbi12d
    c0h
    @6
    wceq
    #
    @18
    @7
    @20
    @10
    c0h
    @6
    @5
    sseq2
    @24
    @19
    @9
    c0h
    c0h
    @6
    @8
    ineq1
    eqeq1d
    anbi12d
    @14
    @17
    c0h
    ssid
    c0h
    csh
    wcel
    @17
    h0elsh
    c0h
    ocin
    ax-mp
    pm3.2i
    elimhyp2v
    #
    simpli
    @7
    @10
    @25
    simpri
    omlsii
    dedth2v
end
