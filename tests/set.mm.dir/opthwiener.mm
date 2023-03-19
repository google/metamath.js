include "csn.mm"
include "c0.mm"
include "cpr.mm"
include "wceq.mm"
include "wa.mm"
include "id.mm"
include "wo.mm"
include "wcel.mm"
include "snex.mm"
include "prid2.mm"
include "eleq2.mm"
include "mpbii.mm"
include "elpr.mm"
include "sylib.mm"
include "wn.mm"
include "wb.mm"
include "0ex.mm"
include "snnz.mm"
include "elsn.mm"
include "eqcom.mm"
include "bitri.mm"
include "nemtbir.mm"
include "nelneq2.mm"
include "mp2an.mm"
include "mtbi.mm"
include "biorf.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "preq2d.mm"
include "eqtr4d.mm"
include "prex.mm"
include "preqr1.mm"
include "syl.mm"
include "sneqr.mm"
include "jca.mm"
include "sneq.mm"
include "preq1d.mm"
include "sylan9eq.mm"
include "impbii.mm"

theorem opthwiener
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume opthw.1: |- A e. _V
  assume opthw.2: |- B e. _V


  assert |- ( { { { A } , (/) } , { { B } } } = { { { C } , (/) } , { { D } } } <-> ( A = C /\ B = D ) )

  proof
    cA
    csn
    #
    c0
    cpr
    #
    cB
    csn
    #
    csn
    #
    cpr
    #
    cC
    csn
    #
    c0
    cpr
    #
    cD
    csn
    #
    csn
    #
    cpr
    #
    wceq
    #
    cA
    cC
    wceq
    #
    cB
    cD
    wceq
    #
    wa
    @10
    @11
    @12
    @10
    @0
    @5
    wceq
    #
    @11
    @10
    @1
    @6
    wceq
    #
    @13
    @10
    @4
    @6
    @3
    cpr
    #
    wceq
    @14
    @10
    @4
    @9
    @15
    @10
    id
    @10
    @3
    @8
    @6
    @10
    @3
    @6
    wceq
    #
    @3
    @8
    wceq
    #
    wo
    #
    @17
    @10
    @3
    @9
    wcel
    #
    @18
    @10
    @3
    @4
    wcel
    @19
    @1
    @3
    @2
    snex
    #
    prid2
    @4
    @9
    @3
    eleq2
    mpbii
    @3
    @6
    @8
    @20
    elpr
    sylib
    @16
    wn
    @17
    @18
    wb
    @6
    @3
    wceq
    #
    @16
    c0
    @6
    wcel
    c0
    @3
    wcel
    #
    wn
    @21
    wn
    @5
    c0
    0ex
    prid2
    @22
    @2
    c0
    cB
    opthw.2
    snnz
    @22
    c0
    @2
    wceq
    @2
    c0
    wceq
    c0
    @2
    0ex
    elsn
    c0
    @2
    eqcom
    bitri
    nemtbir
    c0
    @6
    @3
    nelneq2
    mp2an
    @6
    @3
    eqcom
    mtbi
    @16
    @17
    biorf
    ax-mp
    sylibr
    #
    preq2d
    eqtr4d
    @1
    @6
    @3
    @0
    c0
    prex
    @5
    c0
    prex
    preqr1
    syl
    @0
    @5
    c0
    cA
    snex
    cC
    snex
    preqr1
    syl
    cA
    cC
    opthw.1
    sneqr
    syl
    @10
    @2
    @7
    wceq
    #
    @12
    @10
    @17
    @24
    @23
    @2
    @7
    cB
    snex
    sneqr
    syl
    cB
    cD
    opthw.2
    sneqr
    syl
    jca
    @11
    @12
    @4
    @15
    @9
    @11
    @1
    @6
    @3
    @11
    @0
    @5
    c0
    cA
    cC
    sneq
    preq1d
    preq1d
    @12
    @3
    @8
    @6
    @12
    @24
    @17
    cB
    cD
    sneq
    @2
    @7
    sneq
    syl
    preq2d
    sylan9eq
    impbii
end
