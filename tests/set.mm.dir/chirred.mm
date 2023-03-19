include "cch.mm"
include "wcel.mm"
include "cv.mm"
include "ccm.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "c0h.mm"
include "wceq.mm"
include "chil.mm"
include "wo.mm"
include "cif.mm"
include "eqeq1.mm"
include "orbi12d.mm"
include "eleq1.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "nfcv.mm"
include "nfif.mm"
include "nfeq2.mm"
include "breq1.mm"
include "ralbid.mm"
include "anbi12d.mm"
include "h0elch.mm"
include "cm0.mm"
include "rgen.mm"
include "pm3.2i.mm"
include "elimhyp.mm"
include "simpli.mm"
include "simpri.mm"
include "nfbr.mm"
include "breq2.mm"
include "rspc.mm"
include "mpi.mm"
include "chirredi.mm"
include "dedth.mm"

theorem chirred
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( ( A e. CH /\ A. x e. CH A C_H x ) -> ( A = 0H \/ A = ~H ) )

  proof
    cA
    cch
    wcel
    #
    cA
    vx
    cv
    #
    ccm
    wbr
    #
    vx
    cch
    wral
    #
    wa
    #
    cA
    c0h
    wceq
    #
    cA
    chil
    wceq
    #
    wo
    @4
    cA
    c0h
    cif
    #
    c0h
    wceq
    #
    @7
    chil
    wceq
    #
    wo
    cA
    c0h
    cA
    @7
    wceq
    #
    @5
    @8
    @6
    @9
    cA
    @7
    c0h
    eqeq1
    cA
    @7
    chil
    eqeq1
    orbi12d
    vy
    @7
    @7
    cch
    wcel
    #
    @7
    @1
    ccm
    wbr
    #
    vx
    cch
    wral
    #
    @4
    @11
    @13
    wa
    c0h
    cch
    wcel
    #
    c0h
    @1
    ccm
    wbr
    #
    vx
    cch
    wral
    #
    wa
    cA
    c0h
    @10
    @0
    @11
    @3
    @13
    cA
    @7
    cch
    eleq1
    @10
    @2
    @12
    vx
    cch
    vx
    cA
    @7
    @4
    vx
    cA
    c0h
    @0
    @3
    vx
    @0
    vx
    nfv
    @2
    vx
    cch
    nfra1
    nfan
    vx
    cA
    nfcv
    vx
    c0h
    nfcv
    nfif
    #
    nfeq2
    cA
    @7
    @1
    ccm
    breq1
    ralbid
    anbi12d
    c0h
    @7
    wceq
    #
    @14
    @11
    @16
    @13
    c0h
    @7
    cch
    eleq1
    @18
    @15
    @12
    vx
    cch
    vx
    c0h
    @7
    @17
    nfeq2
    c0h
    @7
    @1
    ccm
    breq1
    ralbid
    anbi12d
    @14
    @16
    h0elch
    @15
    vx
    cch
    @1
    cm0
    rgen
    pm3.2i
    elimhyp
    #
    simpli
    vy
    cv
    #
    cch
    wcel
    @13
    @7
    @20
    ccm
    wbr
    #
    @11
    @13
    @19
    simpri
    @12
    @21
    vx
    @20
    cch
    vx
    @7
    @20
    ccm
    @17
    vx
    ccm
    nfcv
    vx
    @20
    nfcv
    nfbr
    @1
    @20
    @7
    ccm
    breq2
    rspc
    mpi
    chirredi
    dedth
end
