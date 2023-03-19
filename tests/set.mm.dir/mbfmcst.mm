include "cmbfm.mm"
include "co.mm"
include "wcel.mm"
include "cuni.mm"
include "cmap.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "wral.mm"
include "wf.mm"
include "adantr.mm"
include "fmpt3d.mm"
include "csiga.mm"
include "crn.mm"
include "unielsiga.mm"
include "syl.mm"
include "elmapd.mm"
include "mpbird.mm"
include "cmpt.mm"
include "csn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "cxp.mm"
include "cdm.mm"
include "cres.mm"
include "fconstmpt.mm"
include "cnveqi.mm"
include "cnvxp.mm"
include "eqtr3i.mm"
include "imaeq1i.mm"
include "df-ima.mm"
include "df-rn.mm"
include "3eqtri.mm"
include "cvv.mm"
include "df-res.mm"
include "inxp.mm"
include "inv1.mm"
include "xpeq2i.mm"
include "dmeqi.mm"
include "xpeq2.mm"
include "xp0.mm"
include "syl6eq.mm"
include "dmeqd.mm"
include "dm0.mm"
include "adantl.mm"
include "0elsiga.mm"
include "eqeltrd.mm"
include "syl5eqel.mm"
include "wne.mm"
include "dmxp.mm"
include "pm2.61dane.mm"
include "ralrimivw.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "ismbfm.mm"
include "mpbir2and.mm"

theorem mbfmcst
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cT: class T
  let cF: class F
  let vy: setvar y
  assume mbfmcst.1: |- ( ph -> S e. U. ran sigAlgebra )
  assume mbfmcst.2: |- ( ph -> T e. U. ran sigAlgebra )
  assume mbfmcst.3: |- ( ph -> F = ( x e. U. S |-> A ) )
  assume mbfmcst.4: |- ( ph -> A e. U. T )

  disjoint A x
  disjoint S x
  disjoint T x
  disjoint ph x
  disjoint F y
  disjoint x y
  disjoint S y
  disjoint T y
  disjoint ph y
  assert |- ( ph -> F e. ( S MblFnM T ) )

  proof
    wph
    cF
    cS
    cT
    cmbfm
    co
    wcel
    cF
    cT
    cuni
    #
    cS
    cuni
    #
    cmap
    co
    wcel
    #
    cF
    ccnv
    #
    vy
    cv
    #
    cima
    #
    cS
    wcel
    #
    vy
    cT
    wral
    #
    wph
    @2
    @1
    @0
    cF
    wf
    wph
    vx
    @1
    cA
    @0
    cF
    mbfmcst.3
    wph
    cA
    @0
    wcel
    vx
    cv
    @1
    wcel
    mbfmcst.4
    adantr
    fmpt3d
    wph
    @0
    @1
    cF
    cT
    cS
    wph
    cT
    csiga
    crn
    cuni
    #
    wcel
    @0
    cT
    wcel
    mbfmcst.2
    cT
    unielsiga
    syl
    wph
    cS
    @8
    wcel
    #
    @1
    cS
    wcel
    #
    mbfmcst.1
    cS
    unielsiga
    syl
    #
    elmapd
    mpbird
    wph
    @7
    vx
    @1
    cA
    cmpt
    #
    ccnv
    #
    @4
    cima
    #
    cS
    wcel
    #
    vy
    cT
    wral
    wph
    @15
    vy
    cT
    wph
    @15
    cA
    csn
    #
    @4
    cin
    #
    c0
    wph
    @17
    c0
    wceq
    #
    wa
    #
    @14
    @1
    @17
    cxp
    #
    cdm
    #
    cS
    @14
    @16
    @1
    cxp
    #
    @4
    cres
    #
    ccnv
    #
    cdm
    #
    @17
    @1
    cxp
    #
    ccnv
    #
    cdm
    @21
    @14
    @22
    @4
    cima
    @23
    crn
    @25
    @13
    @22
    @4
    @1
    @16
    cxp
    #
    ccnv
    @13
    @22
    @28
    @12
    vx
    @1
    cA
    fconstmpt
    cnveqi
    @1
    @16
    cnvxp
    eqtr3i
    imaeq1i
    @22
    @4
    df-ima
    @23
    df-rn
    3eqtri
    @24
    @27
    @23
    @26
    @23
    @22
    @4
    cvv
    cxp
    cin
    @17
    @1
    cvv
    cin
    #
    cxp
    @26
    @22
    @4
    df-res
    @16
    @1
    @4
    cvv
    inxp
    @29
    @1
    @17
    @1
    inv1
    xpeq2i
    3eqtri
    cnveqi
    dmeqi
    @27
    @20
    @17
    @1
    cnvxp
    dmeqi
    3eqtri
    #
    @19
    @21
    c0
    cS
    @18
    @21
    c0
    wceq
    wph
    @18
    @21
    c0
    cdm
    c0
    @18
    @20
    c0
    @18
    @20
    @1
    c0
    cxp
    c0
    @17
    c0
    @1
    xpeq2
    @1
    xp0
    syl6eq
    dmeqd
    dm0
    syl6eq
    adantl
    wph
    c0
    cS
    wcel
    #
    @18
    wph
    @9
    @31
    mbfmcst.1
    cS
    0elsiga
    syl
    adantr
    eqeltrd
    syl5eqel
    wph
    @17
    c0
    wne
    #
    wa
    #
    @14
    @21
    cS
    @30
    @33
    @21
    @1
    cS
    @32
    @21
    @1
    wceq
    wph
    @1
    @17
    dmxp
    adantl
    wph
    @10
    @32
    @11
    adantr
    eqeltrd
    syl5eqel
    pm2.61dane
    ralrimivw
    wph
    @6
    @15
    vy
    cT
    wph
    @5
    @14
    cS
    wph
    @3
    @13
    @4
    wph
    cF
    @12
    mbfmcst.3
    cnveqd
    imaeq1d
    eleq1d
    ralbidv
    mpbird
    wph
    vy
    cS
    cT
    cF
    mbfmcst.1
    mbfmcst.2
    ismbfm
    mpbir2and
end
