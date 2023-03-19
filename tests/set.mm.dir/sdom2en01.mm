include "c2o.mm"
include "csdm.mm"
include "wbr.mm"
include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "c1o.mm"
include "cen.mm"
include "wo.mm"
include "cdom.mm"
include "com.mm"
include "con0.mm"
include "cin.mm"
include "onfin2.mm"
include "inss2.mm"
include "eqsstri.mm"
include "2onn.mm"
include "sselii.mm"
include "sdomdom.mm"
include "domfi.mm"
include "sylancr.mm"
include "id.mm"
include "0fin.mm"
include "syl6eqel.mm"
include "1onn.mm"
include "enfi.mm"
include "mpbiri.mm"
include "jaoi.mm"
include "ccrd.mm"
include "cfv.mm"
include "wb.mm"
include "cpr.mm"
include "df2o3.mm"
include "eleq2i.mm"
include "fvex.mm"
include "elpr.mm"
include "bitri.mm"
include "a1i.mm"
include "cardnn.mm"
include "ax-mp.mm"
include "cdm.mm"
include "finnum.mm"
include "2on.mm"
include "onenon.mm"
include "cardsdom2.mm"
include "sylancl.mm"
include "syl5bbr.mm"
include "cardnueq0.mm"
include "syl.mm"
include "eqeq2i.mm"
include "carden2.mm"
include "orbi12d.mm"
include "3bitr3d.mm"
include "pm5.21nii.mm"

theorem sdom2en01
  let cA: class A


  assert |- ( A ~< 2o <-> ( A = (/) \/ A ~~ 1o ) )

  proof
    cA
    c2o
    csdm
    wbr
    #
    cA
    cfn
    wcel
    #
    cA
    c0
    wceq
    #
    cA
    c1o
    cen
    wbr
    #
    wo
    #
    @0
    c2o
    cfn
    wcel
    cA
    c2o
    cdom
    wbr
    @1
    com
    cfn
    c2o
    com
    con0
    cfn
    cin
    cfn
    onfin2
    con0
    cfn
    inss2
    eqsstri
    #
    2onn
    sselii
    cA
    c2o
    sdomdom
    c2o
    cA
    domfi
    sylancr
    @2
    @1
    @3
    @2
    cA
    c0
    cfn
    @2
    id
    0fin
    syl6eqel
    @3
    @1
    c1o
    cfn
    wcel
    #
    com
    cfn
    c1o
    @5
    1onn
    sselii
    #
    cA
    c1o
    enfi
    mpbiri
    jaoi
    @1
    cA
    ccrd
    cfv
    #
    c2o
    wcel
    #
    @8
    c0
    wceq
    #
    @8
    c1o
    wceq
    #
    wo
    #
    @0
    @4
    @9
    @12
    wb
    @1
    @9
    @8
    c0
    c1o
    cpr
    #
    wcel
    @12
    c2o
    @13
    @8
    df2o3
    eleq2i
    @8
    c0
    c1o
    cA
    ccrd
    fvex
    elpr
    bitri
    a1i
    @9
    @8
    c2o
    ccrd
    cfv
    #
    wcel
    #
    @1
    @0
    @14
    c2o
    @8
    c2o
    com
    wcel
    @14
    c2o
    wceq
    2onn
    c2o
    cardnn
    ax-mp
    eleq2i
    @1
    cA
    ccrd
    cdm
    #
    wcel
    #
    c2o
    @16
    wcel
    #
    @15
    @0
    wb
    cA
    finnum
    #
    c2o
    con0
    wcel
    @18
    2on
    c2o
    onenon
    ax-mp
    cA
    c2o
    cardsdom2
    sylancl
    syl5bbr
    @1
    @10
    @2
    @11
    @3
    @1
    @17
    @10
    @2
    wb
    @19
    cA
    cardnueq0
    syl
    @11
    @8
    c1o
    ccrd
    cfv
    #
    wceq
    #
    @1
    @3
    @20
    c1o
    @8
    c1o
    com
    wcel
    @20
    c1o
    wceq
    1onn
    c1o
    cardnn
    ax-mp
    eqeq2i
    @1
    @17
    c1o
    @16
    wcel
    #
    @21
    @3
    wb
    @19
    @6
    @22
    @7
    c1o
    finnum
    ax-mp
    cA
    c1o
    carden2
    sylancl
    syl5bbr
    orbi12d
    3bitr3d
    pm5.21nii
end
