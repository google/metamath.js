include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "ccnv.mm"
include "cima.mm"
include "cdm.mm"
include "cin.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "wcel.mm"
include "crab.mm"
include "cmpt.mm"
include "crn.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "uzct.mm"
include "a1i.mm"
include "mptct.mm"
include "rnct.mm"
include "3syl.mm"
include "wrex.mm"
include "c0.mm"
include "wne.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "adantl.mm"
include "wi.mm"
include "w3a.mm"
include "simp3.mm"
include "crest.mm"
include "co.mm"
include "csalg.mm"
include "adantr.mm"
include "csmblfn.mm"
include "ffvelrnda.mm"
include "smfpimbor1.mm"
include "fvex.mm"
include "dmex.mm"
include "elrest.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "rabn0.mm"
include "sylibr.mm"
include "3adant3.mm"
include "eqnetrd.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "axccd2.mm"
include "nfv.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfral.mm"
include "nfan.mm"
include "cuz.mm"
include "eqeltri.mm"
include "fveq2.mm"
include "id.mm"
include "eleq12d.mm"
include "rspccva.mm"
include "adantll.mm"
include "smfpimcclem.mm"
include "ex.mm"
include "exlimdv.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfcnv.mm"
include "nfima.mm"
include "nfdm.mm"
include "nfin.mm"
include "nfeq.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "dmeqd.mm"
include "ineq12d.mm"
include "eqeq12d.mm"
include "cbvral.mm"
include "anbi2i.mm"
include "exbii.mm"
include "sylib.mm"

theorem smfpimcc
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let vh: setvar h
  let vn: setvar n
  let cF: class F
  let cJ: class J
  let cM: class M
  let cZ: class Z
  let vf: setvar f
  let vm: setvar m
  let vs: setvar s
  let vw: setvar w
  let vy: setvar y
  let vk: setvar k
  let vx: setvar x
  assume smfpimcc.1: |- F/_ n F
  assume smfpimcc.z: |- Z = ( ZZ>= ` M )
  assume smfpimcc.s: |- ( ph -> S e. SAlg )
  assume smfpimcc.f: |- ( ph -> F : Z --> ( SMblFn ` S ) )
  assume smfpimcc.j: |- J = ( topGen ` ran (,) )
  assume smfpimcc.b: |- B = ( SalGen ` J )
  assume smfpimcc.a: |- ( ph -> A e. B )

  disjoint A h
  disjoint A n
  disjoint h n
  disjoint F h
  disjoint S h
  disjoint Z h
  disjoint Z n
  disjoint A f
  disjoint A m
  disjoint A s
  disjoint f h
  disjoint f m
  disjoint f s
  disjoint h m
  disjoint h s
  disjoint m s
  disjoint m n
  disjoint A w
  disjoint A y
  disjoint f w
  disjoint f y
  disjoint m w
  disjoint m y
  disjoint s w
  disjoint s y
  disjoint w y
  disjoint F f
  disjoint F m
  disjoint F s
  disjoint F w
  disjoint F y
  disjoint S f
  disjoint S m
  disjoint S s
  disjoint S w
  disjoint S y
  disjoint Z f
  disjoint Z m
  disjoint Z w
  disjoint Z y
  disjoint f ph
  disjoint m ph
  disjoint ph w
  disjoint ph y
  disjoint k x
  assert |- ( ph -> E. h ( h : Z --> S /\ A. n e. Z ( `' ( F ` n ) " A ) = ( ( h ` n ) i^i dom ( F ` n ) ) ) )

  proof
    wph
    cZ
    cS
    vh
    cv
    #
    wf
    #
    vm
    cv
    #
    cF
    cfv
    #
    ccnv
    #
    cA
    cima
    #
    @2
    @0
    cfv
    #
    @3
    cdm
    #
    cin
    #
    wceq
    #
    vm
    cZ
    wral
    #
    wa
    #
    vh
    wex
    #
    @1
    vn
    cv
    #
    cF
    cfv
    #
    ccnv
    #
    cA
    cima
    #
    @13
    @0
    cfv
    #
    @14
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
    wa
    #
    vh
    wex
    wph
    vy
    cv
    #
    vf
    cv
    #
    cfv
    #
    @23
    wcel
    #
    vy
    vm
    cZ
    @5
    vs
    cv
    @7
    cin
    wceq
    #
    vs
    cS
    crab
    #
    cmpt
    #
    crn
    #
    wral
    #
    vf
    wex
    @12
    wph
    vy
    @30
    vf
    wph
    cZ
    com
    cdom
    wbr
    #
    @29
    com
    cdom
    wbr
    @30
    com
    cdom
    wbr
    @32
    wph
    cM
    cZ
    smfpimcc.z
    uzct
    a1i
    vm
    cZ
    @28
    mptct
    @29
    rnct
    3syl
    wph
    @23
    @30
    wcel
    #
    wa
    @23
    @28
    wceq
    #
    vm
    cZ
    wrex
    #
    @23
    c0
    wne
    #
    @33
    @35
    wph
    @33
    @35
    @23
    cvv
    wcel
    @33
    @35
    wb
    vy
    vex
    vm
    cZ
    @28
    @23
    @29
    cvv
    @29
    eqid
    elrnmpt
    ax-mp
    biimpi
    adantl
    wph
    @35
    @36
    wi
    @33
    wph
    @34
    @36
    vm
    cZ
    wph
    @2
    cZ
    wcel
    #
    @34
    @36
    wph
    @37
    @34
    w3a
    @23
    @28
    c0
    wph
    @37
    @34
    simp3
    wph
    @37
    @28
    c0
    wne
    #
    @34
    wph
    @37
    wa
    #
    @27
    vs
    cS
    wrex
    #
    @38
    @39
    @5
    cS
    @7
    crest
    co
    wcel
    #
    @40
    @39
    cB
    @7
    @5
    cS
    cA
    @3
    cJ
    wph
    cS
    csalg
    wcel
    #
    @37
    smfpimcc.s
    adantr
    wph
    cZ
    cS
    csmblfn
    cfv
    @2
    cF
    smfpimcc.f
    ffvelrnda
    @7
    eqid
    smfpimcc.j
    smfpimcc.b
    wph
    cA
    cB
    wcel
    @37
    smfpimcc.a
    adantr
    @5
    eqid
    smfpimbor1
    wph
    @41
    @40
    wb
    #
    @37
    wph
    @42
    @7
    cvv
    wcel
    #
    @43
    smfpimcc.s
    @44
    wph
    @3
    @2
    cF
    fvex
    dmex
    a1i
    vs
    @5
    @7
    cS
    csalg
    cvv
    elrest
    syl2anc
    adantr
    mpbid
    @27
    vs
    cS
    rabn0
    sylibr
    3adant3
    eqnetrd
    3exp
    rexlimdv
    adantr
    mpd
    axccd2
    wph
    @31
    @12
    vf
    wph
    @31
    @12
    wph
    @31
    wa
    vw
    cA
    @24
    cS
    vh
    vm
    cF
    vm
    cZ
    @28
    @24
    cfv
    cmpt
    #
    cvv
    csalg
    cZ
    vs
    wph
    @31
    vm
    wph
    vm
    nfv
    @26
    vm
    vy
    @30
    vm
    @29
    vm
    cZ
    @28
    nfmpt1
    nfrn
    @26
    vm
    nfv
    nfral
    nfan
    cZ
    cM
    cuz
    cfv
    cvv
    smfpimcc.z
    cM
    cuz
    fvex
    eqeltri
    wph
    @42
    @31
    smfpimcc.s
    adantr
    @31
    vw
    cv
    #
    @30
    wcel
    @46
    @24
    cfv
    #
    @46
    wcel
    #
    wph
    @26
    @48
    vy
    @46
    @30
    @23
    @46
    wceq
    #
    @25
    @47
    @23
    @46
    @23
    @46
    @24
    fveq2
    @49
    id
    eleq12d
    rspccva
    adantll
    @45
    eqid
    smfpimcclem
    ex
    exlimdv
    mpd
    @11
    @22
    vh
    @10
    @21
    @1
    @9
    @20
    vm
    vn
    cZ
    vn
    @5
    @8
    vn
    @4
    cA
    vn
    @3
    vn
    @2
    cF
    smfpimcc.1
    vn
    @2
    nfcv
    nffv
    #
    nfcnv
    vn
    cA
    nfcv
    nfima
    vn
    @6
    @7
    vn
    @6
    nfcv
    vn
    @3
    @50
    nfdm
    nfin
    nfeq
    @20
    vm
    nfv
    @2
    @13
    wceq
    #
    @5
    @16
    @8
    @19
    @51
    @4
    @15
    cA
    @51
    @3
    @14
    @2
    @13
    cF
    fveq2
    #
    cnveqd
    imaeq1d
    @51
    @6
    @17
    @7
    @18
    @2
    @13
    @0
    fveq2
    @51
    @3
    @14
    @52
    dmeqd
    ineq12d
    eqeq12d
    cbvral
    anbi2i
    exbii
    sylib
end
