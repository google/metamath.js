include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "ccnv.mm"
include "cima.mm"
include "cdm.mm"
include "cin.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "crab.mm"
include "wcel.mm"
include "nfcv.mm"
include "ssrab2f.mm"
include "cvv.mm"
include "cmpt.mm"
include "crn.mm"
include "eqid.mm"
include "rabexd.mm"
include "adantr.mm"
include "simpl.mm"
include "simpr.mm"
include "elrnmpt1.mm"
include "syl2anc.mm"
include "jca.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "id.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "sylc.mm"
include "sseldi.mm"
include "fmptdf.mm"
include "nfrab1.mm"
include "nffv.mm"
include "nfin.mm"
include "nfeq.mm"
include "ineq1.mm"
include "eqeq2d.mm"
include "elrabf.mm"
include "sylib.mm"
include "simprd.mm"
include "a1i.mm"
include "elexd.mm"
include "fvmpt2d.mm"
include "ineq1d.mm"
include "eqtr4d.mm"
include "ex.mm"
include "ralrimi.mm"
include "elexi.mm"
include "mptex.mm"
include "eqeltri.mm"
include "feq1.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "fveq1.mm"
include "ralbid.mm"
include "anbi12d.mm"
include "spcev.mm"

theorem smfpimcclem
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cC: class C
  let cS: class S
  let vh: setvar h
  let vn: setvar n
  let cF: class F
  let cH: class H
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x
  assume smfpimcclem.n: |- F/ n ph
  assume smfpimcclem.z: |- Z e. V
  assume smfpimcclem.s: |- ( ph -> S e. W )
  assume smfpimcclem.c: |- ( ( ph /\ y e. ran ( n e. Z |-> { s e. S | ( `' ( F ` n ) " A ) = ( s i^i dom ( F ` n ) ) } ) ) -> ( C ` y ) e. y )
  assume smfpimcclem.h: |- H = ( n e. Z |-> ( C ` { s e. S | ( `' ( F ` n ) " A ) = ( s i^i dom ( F ` n ) ) } ) )

  disjoint A h
  disjoint A s
  disjoint A y
  disjoint s y
  disjoint C s
  disjoint C y
  disjoint F h
  disjoint F s
  disjoint F y
  disjoint H h
  disjoint S h
  disjoint S n
  disjoint h n
  disjoint S s
  disjoint S y
  disjoint n s
  disjoint n y
  disjoint Z h
  disjoint Z n
  disjoint Z y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> E. h ( h : Z --> S /\ A. n e. Z ( `' ( F ` n ) " A ) = ( ( h ` n ) i^i dom ( F ` n ) ) ) )

  proof
    wph
    cZ
    cS
    cH
    wf
    #
    vn
    cv
    #
    cF
    cfv
    #
    ccnv
    cA
    cima
    #
    @1
    cH
    cfv
    #
    @2
    cdm
    #
    cin
    #
    wceq
    #
    vn
    cZ
    wral
    #
    cZ
    cS
    vh
    cv
    #
    wf
    #
    @3
    @1
    @9
    cfv
    #
    @5
    cin
    #
    wceq
    #
    vn
    cZ
    wral
    #
    wa
    #
    vh
    wex
    wph
    vn
    cZ
    @3
    vs
    cv
    #
    @5
    cin
    #
    wceq
    #
    vs
    cS
    crab
    #
    cC
    cfv
    #
    cS
    cH
    smfpimcclem.n
    wph
    @1
    cZ
    wcel
    #
    wa
    #
    @19
    cS
    @20
    @18
    vs
    cS
    vs
    cS
    nfcv
    #
    ssrab2f
    @22
    @19
    cvv
    wcel
    #
    wph
    @19
    vn
    cZ
    @19
    cmpt
    #
    crn
    #
    wcel
    #
    wa
    #
    @20
    @19
    wcel
    #
    wph
    @24
    @21
    wph
    @18
    vs
    cS
    @19
    cW
    @19
    eqid
    smfpimcclem.s
    rabexd
    adantr
    #
    @22
    wph
    @27
    wph
    @21
    simpl
    @22
    @21
    @24
    @27
    wph
    @21
    simpr
    @30
    vn
    cZ
    @19
    @25
    cvv
    @25
    eqid
    elrnmpt1
    syl2anc
    jca
    wph
    vy
    cv
    #
    @26
    wcel
    #
    wa
    #
    @31
    cC
    cfv
    #
    @31
    wcel
    #
    wi
    @28
    @29
    wi
    vy
    @19
    cvv
    @31
    @19
    wceq
    #
    @33
    @28
    @35
    @29
    @36
    @32
    @27
    wph
    @31
    @19
    @26
    eleq1
    anbi2d
    @36
    @34
    @20
    @31
    @19
    @31
    @19
    cC
    fveq2
    @36
    id
    eleq12d
    imbi12d
    smfpimcclem.c
    vtoclg
    sylc
    #
    sseldi
    smfpimcclem.h
    fmptdf
    wph
    @7
    vn
    cZ
    smfpimcclem.n
    wph
    @21
    @7
    @22
    @3
    @20
    @5
    cin
    #
    @6
    @22
    @20
    cS
    wcel
    #
    @3
    @38
    wceq
    #
    @22
    @29
    @39
    @40
    wa
    @37
    @18
    @40
    vs
    @20
    cS
    vs
    @19
    cC
    vs
    cC
    nfcv
    @18
    vs
    cS
    nfrab1
    nffv
    #
    @23
    vs
    @3
    @38
    vs
    @3
    nfcv
    vs
    @20
    @5
    @41
    vs
    @5
    nfcv
    nfin
    nfeq
    @16
    @20
    wceq
    @17
    @38
    @3
    @16
    @20
    @5
    ineq1
    eqeq2d
    elrabf
    sylib
    simprd
    @22
    @4
    @20
    @5
    wph
    vn
    cZ
    @20
    cH
    cvv
    cH
    vn
    cZ
    @20
    cmpt
    #
    wceq
    wph
    smfpimcclem.h
    a1i
    @22
    @20
    @19
    @37
    elexd
    fvmpt2d
    ineq1d
    eqtr4d
    ex
    ralrimi
    @15
    @0
    @8
    wa
    vh
    cH
    cH
    @42
    cvv
    smfpimcclem.h
    vn
    cZ
    @20
    cZ
    cV
    smfpimcclem.z
    elexi
    mptex
    eqeltri
    @9
    cH
    wceq
    #
    @10
    @0
    @14
    @8
    cZ
    cS
    @9
    cH
    feq1
    @43
    @13
    @7
    vn
    cZ
    vn
    @9
    cH
    vn
    @9
    nfcv
    vn
    cH
    @42
    smfpimcclem.h
    vn
    cZ
    @20
    nfmpt1
    nfcxfr
    nfeq
    @43
    @12
    @6
    @3
    @43
    @11
    @4
    @5
    @1
    @9
    cH
    fveq1
    ineq1d
    eqeq2d
    ralbid
    anbi12d
    spcev
    syl2anc
end
