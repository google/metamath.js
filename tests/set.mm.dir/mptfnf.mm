include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "cv.mm"
include "wceq.mm"
include "weu.mm"
include "cmpt.mm"
include "wfn.mm"
include "eueq.mm"
include "ralbii.mm"
include "wex.mm"
include "wmo.mm"
include "wa.mm"
include "r19.26.mm"
include "eu5.mm"
include "copab.mm"
include "wfun.mm"
include "cdm.mm"
include "df-mpt.mm"
include "fneq1i.mm"
include "df-fn.mm"
include "bitri.mm"
include "wal.mm"
include "wi.mm"
include "moanimv.mm"
include "albii.mm"
include "funopab.mm"
include "df-ral.mm"
include "3bitr4ri.mm"
include "cab.mm"
include "eqcom.mm"
include "dmopab.mm"
include "19.42v.mm"
include "abbii.mm"
include "eqtri.mm"
include "eqeq1i.mm"
include "wb.mm"
include "pm4.71.mm"
include "abeq2f.mm"
include "3bitr4i.mm"
include "anbi12i.mm"
include "ancom.mm"
include "3bitr2i.mm"
include "bitr4i.mm"

theorem mptfnf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume mptfnf.0: |- F/_ x A


  assert |- ( A. x e. A B e. _V <-> ( x e. A |-> B ) Fn A )

  proof
    cB
    cvv
    wcel
    #
    vx
    cA
    wral
    vy
    cv
    cB
    wceq
    #
    vy
    weu
    #
    vx
    cA
    wral
    #
    vx
    cA
    cB
    cmpt
    #
    cA
    wfn
    #
    @0
    @2
    vx
    cA
    vy
    cB
    eueq
    ralbii
    @1
    vy
    wex
    #
    @1
    vy
    wmo
    #
    wa
    #
    vx
    cA
    wral
    @6
    vx
    cA
    wral
    #
    @7
    vx
    cA
    wral
    #
    wa
    #
    @3
    @5
    @6
    @7
    vx
    cA
    r19.26
    @2
    @8
    vx
    cA
    @1
    vy
    eu5
    ralbii
    @5
    vx
    cv
    cA
    wcel
    #
    @1
    wa
    #
    vx
    vy
    copab
    #
    wfun
    #
    @14
    cdm
    #
    cA
    wceq
    #
    wa
    #
    @10
    @9
    wa
    @11
    @5
    @14
    cA
    wfn
    @18
    cA
    @4
    @14
    vx
    vy
    cA
    cB
    df-mpt
    fneq1i
    @14
    cA
    df-fn
    bitri
    @10
    @15
    @9
    @17
    @13
    vy
    wmo
    #
    vx
    wal
    @12
    @7
    wi
    #
    vx
    wal
    @15
    @10
    @19
    @20
    vx
    @12
    @1
    vy
    moanimv
    albii
    @13
    vx
    vy
    funopab
    @7
    vx
    cA
    df-ral
    3bitr4ri
    @12
    @6
    wa
    #
    vx
    cab
    #
    cA
    wceq
    cA
    @22
    wceq
    #
    @17
    @9
    @22
    cA
    eqcom
    @16
    @22
    cA
    @16
    @13
    vy
    wex
    #
    vx
    cab
    @22
    @13
    vx
    vy
    dmopab
    @24
    @21
    vx
    @12
    @1
    vy
    19.42v
    abbii
    eqtri
    eqeq1i
    @12
    @6
    wi
    #
    vx
    wal
    @12
    @21
    wb
    #
    vx
    wal
    @9
    @23
    @25
    @26
    vx
    @12
    @6
    pm4.71
    albii
    @6
    vx
    cA
    df-ral
    @21
    vx
    cA
    mptfnf.0
    abeq2f
    3bitr4i
    3bitr4ri
    anbi12i
    @10
    @9
    ancom
    3bitr2i
    3bitr4ri
    bitr4i
end
