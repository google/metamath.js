include "cv.mm"
include "cep.mm"
include "wbr.mm"
include "wn.mm"
include "com.mm"
include "cfv.mm"
include "cmpt.mm"
include "crn.mm"
include "wral.mm"
include "wrex.mm"
include "csuc.mm"
include "wnel.mm"
include "cvv.mm"
include "wcel.mm"
include "wfr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "omex.mm"
include "mptex.mm"
include "rnex.mm"
include "zfregfr.mm"
include "ssid.mm"
include "cdm.mm"
include "wceq.mm"
include "dmmptg.mm"
include "fvexd.mm"
include "mprg.mm"
include "peano1.mm"
include "ne0ii.mm"
include "eqnetri.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "mpbi.mm"
include "fri.mm"
include "mp4an.mm"
include "wfn.mm"
include "wb.mm"
include "fvex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "fvelrnb.mm"
include "ax-mp.mm"
include "wi.mm"
include "peano2.mm"
include "fveq2.mm"
include "fvmpt.mm"
include "syl.mm"
include "fnfvelrn.mm"
include "sylancr.mm"
include "eqeltrrd.mm"
include "wel.mm"
include "epel.mm"
include "eleq1.mm"
include "syl5bb.mm"
include "notbid.mm"
include "df-nel.mm"
include "syl6bbr.mm"
include "rspccv.mm"
include "syl5com.mm"
include "eqeq1.mm"
include "syl5ibcom.mm"
include "neleq2.mm"
include "biimpd.mm"
include "syl6.mm"
include "com23.mm"
include "syldc.mm"
include "reximdvai.mm"
include "syl5bi.mm"
include "com12.mm"
include "rexlimiv.mm"

theorem noinfep
  let vx: setvar x
  let cF: class F
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z

  disjoint F x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  assert |- E. x e. _om ( F ` suc x ) e/ ( F ` x )

  proof
    vz
    cv
    #
    vy
    cv
    #
    cep
    wbr
    #
    wn
    #
    vz
    vw
    com
    vw
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    crn
    #
    wral
    #
    vy
    @7
    wrex
    #
    vx
    cv
    #
    csuc
    #
    cF
    cfv
    #
    @10
    cF
    cfv
    #
    wnel
    #
    vx
    com
    wrex
    #
    @7
    cvv
    wcel
    @7
    cep
    wfr
    @7
    @7
    wss
    @7
    c0
    wne
    #
    @9
    @6
    vw
    com
    @5
    omex
    mptex
    rnex
    @7
    zfregfr
    @7
    ssid
    @6
    cdm
    #
    c0
    wne
    @16
    @17
    com
    c0
    @5
    cvv
    wcel
    @17
    com
    wceq
    vw
    com
    vw
    com
    @5
    cvv
    dmmptg
    @4
    com
    wcel
    @4
    cF
    fvexd
    mprg
    c0
    com
    peano1
    ne0ii
    eqnetri
    @17
    c0
    @7
    c0
    @6
    dm0rn0
    necon3bii
    mpbi
    vy
    vz
    @7
    @7
    cvv
    cep
    fri
    mp4an
    @8
    @15
    vy
    @7
    @8
    @1
    @7
    wcel
    #
    @15
    @18
    @10
    @6
    cfv
    #
    @1
    wceq
    #
    vx
    com
    wrex
    #
    @8
    @15
    @6
    com
    wfn
    #
    @18
    @21
    wb
    vw
    com
    @5
    @6
    @4
    cF
    fvex
    @6
    eqid
    #
    fnmpti
    #
    vx
    com
    @1
    @6
    fvelrnb
    ax-mp
    @8
    @20
    @14
    vx
    com
    @10
    com
    wcel
    #
    @8
    @12
    @1
    wnel
    #
    @20
    @14
    wi
    @25
    @12
    @7
    wcel
    @8
    @26
    @25
    @11
    @6
    cfv
    #
    @12
    @7
    @25
    @11
    com
    wcel
    #
    @27
    @12
    wceq
    @10
    peano2
    #
    vw
    @11
    @5
    @12
    com
    @6
    @4
    @11
    cF
    fveq2
    @23
    @11
    cF
    fvex
    fvmpt
    syl
    @25
    @22
    @28
    @27
    @7
    wcel
    @24
    @29
    com
    @11
    @6
    fnfvelrn
    sylancr
    eqeltrrd
    @3
    @26
    vz
    @12
    @7
    @0
    @12
    wceq
    #
    @3
    @12
    @1
    wcel
    #
    wn
    @26
    @30
    @2
    @31
    @2
    vz
    vy
    wel
    @30
    @31
    vz
    vy
    epel
    @0
    @12
    @1
    eleq1
    syl5bb
    notbid
    @12
    @1
    df-nel
    syl6bbr
    rspccv
    syl5com
    @25
    @20
    @26
    @14
    @25
    @20
    @1
    @13
    wceq
    #
    @26
    @14
    wi
    @25
    @19
    @13
    wceq
    @20
    @32
    vw
    @10
    @5
    @13
    com
    @6
    @4
    @10
    cF
    fveq2
    @23
    @10
    cF
    fvex
    fvmpt
    @19
    @1
    @13
    eqeq1
    syl5ibcom
    @32
    @26
    @14
    @1
    @13
    @12
    neleq2
    biimpd
    syl6
    com23
    syldc
    reximdvai
    syl5bi
    com12
    rexlimiv
    ax-mp
end
