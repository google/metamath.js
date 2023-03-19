include "cfn.mm"
include "wcel.mm"
include "cdm.mm"
include "crn.mm"
include "wa.mm"
include "c0.mm"
include "csupp.mm"
include "co.mm"
include "wss.mm"
include "cv.mm"
include "cfv.mm"
include "copab.mm"
include "wceq.mm"
include "wrel.mm"
include "wb.mm"
include "relopab.mm"
include "releq.mm"
include "mpbiri.mm"
include "relfi.mm"
include "3syl.mm"
include "wex.mm"
include "cab.mm"
include "wrex.mm"
include "cuni.mm"
include "rexcom4.mm"
include "ancom.mm"
include "exbii.mm"
include "fvex.mm"
include "eleq2.mm"
include "ceqsexv.mm"
include "bitr3i.mm"
include "rexbii.mm"
include "r19.42v.mm"
include "3bitr3ri.mm"
include "df-rex.mm"
include "bitr2i.mm"
include "a1i.mm"
include "vex.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "elab.mm"
include "eluniab.mm"
include "3bitr4g.mm"
include "eqrdv.mm"
include "eleq1d.mm"
include "adantr.mm"
include "wi.mm"
include "cpw.mm"
include "wf.mm"
include "wfn.mm"
include "ffn.mm"
include "fnrnfv.mm"
include "cvv.mm"
include "0ex.mm"
include "fex.mm"
include "sylancl.mm"
include "wfun.mm"
include "ffun.mm"
include "syl.mm"
include "opabdm.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "cmpt.mm"
include "ccnv.mm"
include "cima.mm"
include "mpan2.mm"
include "suppimacnv.mm"
include "feqmptd.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "eqtrd.mm"
include "eqid.mm"
include "mptpreima.mm"
include "syl6eq.mm"
include "wne.mm"
include "suppvalfn.mm"
include "mp3an23.mm"
include "n0.mm"
include "rabbii.mm"
include "3eqtr3d.mm"
include "df-rab.mm"
include "19.42v.mm"
include "abbii.mm"
include "eqtr4i.mm"
include "3eqtrd.mm"
include "eqtr4d.mm"
include "biimpa.mm"
include "ffsrn.mm"
include "eqeltrrd.mm"
include "unifi.mm"
include "ex.mm"
include "unifi3.mm"
include "impbid1.mm"
include "bitr4d.mm"
include "opabrn.mm"
include "sseq1d.mm"
include "3bitr4d.mm"
include "pm5.32da.mm"
include "anbi1d.mm"
include "bitrd.mm"
include "3bitrd.mm"

theorem fpwrelmapffslem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let vw: setvar w
  let vz: setvar z
  assume fpwrelmapffslem.1: |- A e. _V
  assume fpwrelmapffslem.2: |- B e. _V
  assume fpwrelmapffslem.3: |- ( ph -> F : A --> ~P B )
  assume fpwrelmapffslem.4: |- ( ph -> R = { <. x , y >. | ( x e. A /\ y e. ( F ` x ) ) } )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F x
  disjoint F y
  disjoint R x
  disjoint R y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint F w
  disjoint F z
  disjoint ph w
  assert |- ( ph -> ( R e. Fin <-> ( ran F C_ Fin /\ ( F supp (/) ) e. Fin ) ) )

  proof
    wph
    cR
    cfn
    wcel
    #
    cR
    cdm
    #
    cfn
    wcel
    #
    cR
    crn
    #
    cfn
    wcel
    #
    wa
    #
    cF
    c0
    csupp
    co
    #
    cfn
    wcel
    #
    cF
    crn
    #
    cfn
    wss
    #
    wa
    #
    @9
    @7
    wa
    #
    wph
    cR
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    @12
    cF
    cfv
    #
    wcel
    #
    wa
    #
    vx
    vy
    copab
    #
    wceq
    #
    cR
    wrel
    #
    @0
    @5
    wb
    fpwrelmapffslem.4
    @19
    @20
    @18
    wrel
    @17
    vx
    vy
    relopab
    cR
    @18
    releq
    mpbiri
    cR
    relfi
    3syl
    wph
    @5
    @2
    @9
    wa
    @10
    wph
    @2
    @4
    @9
    wph
    @2
    wa
    #
    @17
    vx
    wex
    #
    vy
    cab
    #
    cfn
    wcel
    #
    vz
    cv
    #
    @15
    wceq
    #
    vx
    cA
    wrex
    #
    vz
    cab
    #
    cfn
    wss
    #
    @4
    @9
    @21
    @24
    @28
    cuni
    #
    cfn
    wcel
    #
    @29
    wph
    @24
    @31
    wb
    @2
    wph
    @23
    @30
    cfn
    wph
    vw
    @23
    @30
    wph
    @13
    vw
    cv
    #
    @15
    wcel
    #
    wa
    #
    vx
    wex
    #
    @32
    @25
    wcel
    #
    @27
    wa
    #
    vz
    wex
    #
    @32
    @23
    wcel
    @32
    @30
    wcel
    @35
    @38
    wb
    wph
    @38
    @33
    vx
    cA
    wrex
    #
    @35
    @36
    @26
    wa
    #
    vz
    wex
    #
    vx
    cA
    wrex
    @40
    vx
    cA
    wrex
    #
    vz
    wex
    @39
    @38
    @40
    vx
    vz
    cA
    rexcom4
    @41
    @33
    vx
    cA
    @41
    @26
    @36
    wa
    #
    vz
    wex
    @33
    @43
    @40
    vz
    @26
    @36
    ancom
    exbii
    @36
    @33
    vz
    @15
    @12
    cF
    fvex
    @25
    @15
    @32
    eleq2
    ceqsexv
    bitr3i
    rexbii
    @42
    @37
    vz
    @36
    @26
    vx
    cA
    r19.42v
    exbii
    3bitr3ri
    @33
    vx
    cA
    df-rex
    bitr2i
    a1i
    @22
    @35
    vy
    @32
    vw
    vex
    @14
    @32
    wceq
    #
    @17
    @34
    vx
    @44
    @16
    @33
    @13
    @14
    @32
    @15
    eleq1
    anbi2d
    exbidv
    elab
    @27
    vz
    @32
    eluniab
    3bitr4g
    eqrdv
    eleq1d
    adantr
    @21
    @29
    @31
    @21
    @28
    cfn
    wcel
    #
    @29
    @31
    wi
    @21
    @8
    @28
    cfn
    wph
    @8
    @28
    wceq
    #
    @2
    wph
    cA
    cB
    cpw
    #
    cF
    wf
    #
    cF
    cA
    wfn
    #
    @46
    fpwrelmapffslem.3
    cA
    @47
    cF
    ffn
    #
    vx
    vz
    cA
    cF
    fnrnfv
    3syl
    adantr
    #
    @21
    cF
    cvv
    cvv
    c0
    c0
    cvv
    wcel
    #
    @21
    0ex
    a1i
    wph
    cF
    cvv
    wcel
    #
    @2
    wph
    @48
    cA
    cvv
    wcel
    #
    @53
    fpwrelmapffslem.3
    fpwrelmapffslem.1
    cA
    @47
    cvv
    cF
    fex
    #
    sylancl
    adantr
    wph
    cF
    wfun
    #
    @2
    wph
    @48
    @56
    fpwrelmapffslem.3
    cA
    @47
    cF
    ffun
    syl
    adantr
    wph
    @2
    @7
    wph
    @1
    @6
    cfn
    wph
    @1
    @17
    vy
    wex
    #
    vx
    cab
    #
    @6
    wph
    @19
    @1
    @58
    wceq
    fpwrelmapffslem.4
    @17
    vx
    vy
    cR
    opabdm
    syl
    wph
    @6
    @15
    cvv
    c0
    csn
    cdif
    #
    wcel
    vx
    cA
    crab
    #
    @16
    vy
    wex
    #
    vx
    cA
    crab
    #
    @58
    wph
    @6
    vx
    cA
    @15
    cmpt
    #
    ccnv
    #
    @59
    cima
    #
    @60
    wph
    @6
    cF
    ccnv
    #
    @59
    cima
    #
    @65
    wph
    @48
    @53
    @6
    @67
    wceq
    #
    fpwrelmapffslem.3
    @48
    @54
    @53
    fpwrelmapffslem.1
    @55
    mpan2
    @53
    @52
    @68
    0ex
    cF
    cvv
    cvv
    c0
    suppimacnv
    mpan2
    3syl
    wph
    @66
    @64
    @59
    wph
    cF
    @63
    wph
    vx
    cA
    @47
    cF
    fpwrelmapffslem.3
    feqmptd
    cnveqd
    imaeq1d
    eqtrd
    vx
    cA
    @15
    @59
    @63
    @63
    eqid
    mptpreima
    syl6eq
    #
    wph
    @6
    @15
    c0
    wne
    #
    vx
    cA
    crab
    #
    @60
    @62
    wph
    @48
    @49
    @6
    @71
    wceq
    #
    fpwrelmapffslem.3
    @50
    @49
    @54
    @52
    @72
    fpwrelmapffslem.1
    0ex
    vx
    cF
    cvv
    cvv
    cA
    c0
    suppvalfn
    mp3an23
    3syl
    @69
    @71
    @62
    wceq
    wph
    @70
    @61
    vx
    cA
    vy
    @15
    n0
    rabbii
    a1i
    3eqtr3d
    @62
    @58
    wceq
    wph
    @62
    @13
    @61
    wa
    #
    vx
    cab
    @58
    @61
    vx
    cA
    df-rab
    @57
    @73
    vx
    @13
    @16
    vy
    19.42v
    abbii
    eqtr4i
    a1i
    3eqtrd
    eqtr4d
    eleq1d
    #
    biimpa
    ffsrn
    eqeltrrd
    @45
    @29
    @31
    @28
    unifi
    ex
    syl
    @28
    unifi3
    impbid1
    bitr4d
    wph
    @4
    @24
    wb
    @2
    wph
    @3
    @23
    cfn
    wph
    @19
    @3
    @23
    wceq
    fpwrelmapffslem.4
    @17
    vx
    vy
    cR
    opabrn
    syl
    eleq1d
    adantr
    @21
    @8
    @28
    cfn
    @51
    sseq1d
    3bitr4d
    pm5.32da
    wph
    @2
    @7
    @9
    @74
    anbi1d
    bitrd
    @10
    @11
    wb
    wph
    @7
    @9
    ancom
    a1i
    3bitrd
end
