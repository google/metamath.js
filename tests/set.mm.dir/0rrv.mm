include "cdm.mm"
include "cuni.mm"
include "cc0.mm"
include "cmpt.mm"
include "crrv.mm"
include "cfv.mm"
include "wcel.mm"
include "cr.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cbrsiga.mm"
include "wral.mm"
include "0re.mm"
include "rgenw.mm"
include "eqid.mm"
include "fmpt.mm"
include "mpbi.mm"
include "a1i.mm"
include "csn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "cxp.mm"
include "cres.mm"
include "crn.mm"
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
include "cprb.mm"
include "csiga.mm"
include "domprobsiga.mm"
include "0elsiga.mm"
include "3syl.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "syl5eqel.mm"
include "wne.mm"
include "dmxp.mm"
include "unveldomd.mm"
include "pm2.61dane.mm"
include "ralrimivw.mm"
include "isrrvv.mm"
include "mpbir2and.mm"

theorem 0rrv
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let vy: setvar y
  assume 0rrv.1: |- ( ph -> P e. Prob )

  disjoint P x
  disjoint x y
  disjoint P y
  disjoint ph y
  assert |- ( ph -> ( x e. U. dom P |-> 0 ) e. ( rRndVar ` P ) )

  proof
    wph
    vx
    cP
    cdm
    #
    cuni
    #
    cc0
    cmpt
    #
    cP
    crrv
    cfv
    wcel
    @1
    cr
    @2
    wf
    #
    @2
    ccnv
    #
    vy
    cv
    #
    cima
    #
    @0
    wcel
    #
    vy
    cbrsiga
    wral
    @3
    wph
    cc0
    cr
    wcel
    #
    vx
    @1
    wral
    @3
    @8
    vx
    @1
    0re
    rgenw
    vx
    @1
    cr
    cc0
    @2
    @2
    eqid
    fmpt
    mpbi
    a1i
    wph
    @7
    vy
    cbrsiga
    wph
    @7
    cc0
    csn
    #
    @5
    cin
    #
    c0
    wph
    @10
    c0
    wceq
    #
    wa
    #
    @6
    @1
    @10
    cxp
    #
    cdm
    #
    @0
    @6
    @9
    @1
    cxp
    #
    @5
    cres
    #
    ccnv
    #
    cdm
    #
    @10
    @1
    cxp
    #
    ccnv
    #
    cdm
    @14
    @6
    @15
    @5
    cima
    @16
    crn
    @18
    @4
    @15
    @5
    @1
    @9
    cxp
    #
    ccnv
    @4
    @15
    @21
    @2
    vx
    @1
    cc0
    fconstmpt
    cnveqi
    @1
    @9
    cnvxp
    eqtr3i
    imaeq1i
    @15
    @5
    df-ima
    @16
    df-rn
    3eqtri
    @17
    @20
    @16
    @19
    @16
    @15
    @5
    cvv
    cxp
    cin
    @10
    @1
    cvv
    cin
    #
    cxp
    @19
    @15
    @5
    df-res
    @9
    @1
    @5
    cvv
    inxp
    @22
    @1
    @10
    @1
    inv1
    xpeq2i
    3eqtri
    cnveqi
    dmeqi
    @20
    @13
    @10
    @1
    cnvxp
    dmeqi
    3eqtri
    #
    @12
    @14
    c0
    @0
    @11
    @14
    c0
    wceq
    wph
    @11
    @14
    c0
    cdm
    c0
    @11
    @13
    c0
    @11
    @13
    @1
    c0
    cxp
    c0
    @10
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
    @0
    wcel
    #
    @11
    wph
    cP
    cprb
    wcel
    @0
    csiga
    crn
    cuni
    wcel
    @24
    0rrv.1
    cP
    domprobsiga
    @0
    0elsiga
    3syl
    adantr
    eqeltrd
    syl5eqel
    wph
    @10
    c0
    wne
    #
    wa
    #
    @6
    @14
    @0
    @23
    @26
    @14
    @1
    @0
    @25
    @14
    @1
    wceq
    wph
    @1
    @10
    dmxp
    adantl
    wph
    @1
    @0
    wcel
    @25
    wph
    cP
    0rrv.1
    unveldomd
    adantr
    eqeltrd
    syl5eqel
    pm2.61dane
    ralrimivw
    wph
    vy
    cP
    @2
    0rrv.1
    isrrvv
    mpbir2and
end
