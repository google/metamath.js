include "wfn.mm"
include "c1st.mm"
include "cvv.mm"
include "cxp.mm"
include "cres.mm"
include "ccnv.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "ciun.mm"
include "ccom.mm"
include "cfv.mm"
include "coiun.mm"
include "cdm.mm"
include "crn.mm"
include "cin.mm"
include "wss.mm"
include "wceq.mm"
include "inss1.mm"
include "fndm.mm"
include "syl5sseq.mm"
include "dfco2a.mm"
include "syl.mm"
include "coeq2d.mm"
include "wcel.mm"
include "wa.mm"
include "dmxpss.mm"
include "sstri.mm"
include "ax-mp.mm"
include "fvex.mm"
include "fparlem1.mm"
include "sneq.mm"
include "xpeq1d.mm"
include "syl5eq.mm"
include "imaeq2d.mm"
include "df-ima.mm"
include "ssid.mm"
include "xpssres.mm"
include "rneqi.mm"
include "c0.mm"
include "wne.mm"
include "snnz.mm"
include "rnxp.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "xpeq12d.mm"
include "iunxsn.mm"
include "cnveqi.mm"
include "cnvco.mm"
include "cnvxp.mm"
include "3eqtr3i.mm"
include "xpeq2i.mm"
include "fnsnfv.mm"
include "syl5eqr.mm"
include "cnveqd.mm"
include "iuneq2dv.mm"
include "3eqtr4a.mm"

theorem fparlem3
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cB: class B
  let vy: setvar y
  let cG: class G

  disjoint A x
  disjoint F x
  disjoint B y
  disjoint x y
  disjoint F y
  disjoint G x
  disjoint G y
  assert |- ( F Fn A -> ( `' ( 1st |` ( _V X. _V ) ) o. ( F o. ( 1st |` ( _V X. _V ) ) ) ) = U_ x e. A ( ( { x } X. _V ) X. ( { ( F ` x ) } X. _V ) ) )

  proof
    cF
    cA
    wfn
    #
    c1st
    cvv
    cvv
    cxp
    cres
    #
    ccnv
    #
    vx
    cA
    @2
    vx
    cv
    #
    csn
    #
    cima
    #
    cF
    @4
    cima
    #
    cxp
    #
    ciun
    #
    ccom
    vx
    cA
    @2
    @7
    ccom
    #
    ciun
    @2
    cF
    @1
    ccom
    #
    ccom
    vx
    cA
    @4
    cvv
    cxp
    #
    @3
    cF
    cfv
    #
    csn
    #
    cvv
    cxp
    #
    cxp
    #
    ciun
    vx
    @2
    @7
    cA
    coiun
    @0
    @10
    @8
    @2
    @0
    cF
    cdm
    #
    @1
    crn
    #
    cin
    #
    cA
    wss
    @10
    @8
    wceq
    @0
    @16
    @18
    cA
    @16
    @17
    inss1
    cA
    cF
    fndm
    syl5sseq
    vx
    cF
    @1
    cA
    dfco2a
    syl
    coeq2d
    @0
    vx
    cA
    @15
    @9
    @0
    @3
    cA
    wcel
    wa
    #
    @15
    @2
    @13
    @11
    cxp
    #
    ccnv
    #
    ccom
    #
    @9
    @20
    @1
    ccom
    #
    ccnv
    @14
    @11
    cxp
    #
    ccnv
    @22
    @15
    @23
    @24
    @23
    vy
    @13
    @2
    vy
    cv
    #
    csn
    #
    cima
    #
    @20
    @26
    cima
    #
    cxp
    #
    ciun
    #
    @24
    @20
    cdm
    #
    @17
    cin
    #
    @13
    wss
    @23
    @30
    wceq
    @32
    @31
    @13
    @31
    @17
    inss1
    @13
    @11
    dmxpss
    sstri
    vy
    @20
    @1
    @13
    dfco2a
    ax-mp
    vy
    @12
    @29
    @24
    @3
    cF
    fvex
    #
    @25
    @12
    wceq
    #
    @27
    @14
    @28
    @11
    @34
    @27
    @26
    cvv
    cxp
    @14
    vy
    fparlem1
    @34
    @26
    @13
    cvv
    @25
    @12
    sneq
    #
    xpeq1d
    syl5eq
    @34
    @28
    @20
    @13
    cima
    #
    @11
    @34
    @26
    @13
    @20
    @35
    imaeq2d
    @36
    @20
    @13
    cres
    #
    crn
    #
    @11
    @20
    @13
    df-ima
    @38
    @20
    crn
    #
    @11
    @37
    @20
    @13
    @13
    wss
    @37
    @20
    wceq
    @13
    ssid
    @13
    @11
    @13
    xpssres
    ax-mp
    rneqi
    @13
    c0
    wne
    @39
    @11
    wceq
    @12
    @33
    snnz
    @13
    @11
    rnxp
    ax-mp
    eqtri
    eqtri
    syl6eq
    xpeq12d
    iunxsn
    eqtri
    cnveqi
    @20
    @1
    cnvco
    @14
    @11
    cnvxp
    3eqtr3i
    @19
    @21
    @7
    @2
    @19
    @21
    @6
    @5
    cxp
    #
    ccnv
    @7
    @19
    @20
    @40
    @19
    @20
    @13
    @5
    cxp
    @40
    @5
    @11
    @13
    vx
    fparlem1
    xpeq2i
    @19
    @13
    @6
    @5
    cA
    @3
    cF
    fnsnfv
    xpeq1d
    syl5eqr
    cnveqd
    @6
    @5
    cnvxp
    syl6eq
    coeq2d
    syl5eqr
    iuneq2dv
    3eqtr4a
end
