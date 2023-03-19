include "clsp.mm"
include "cfv.mm"
include "cr.mm"
include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cxr.mm"
include "cin.mm"
include "clt.mm"
include "csup.mm"
include "cmpt.mm"
include "cinf.mm"
include "cuz.mm"
include "cres.mm"
include "crn.mm"
include "cvv.mm"
include "eqid.mm"
include "wcel.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "fexd.mm"
include "elexd.mm"
include "wss.mm"
include "uzssre.mm"
include "eqsstri.mm"
include "cz.mm"
include "wceq.mm"
include "uzsup.mm"
include "syl.mm"
include "limsupval2.mm"
include "mptima2.mm"
include "oveq1.mm"
include "imaeq2d.mm"
include "ineq1d.mm"
include "supeq1d.mm"
include "cbvmptv.mm"
include "wa.mm"
include "wf.mm"
include "fimass.mm"
include "df-ss.mm"
include "biimpi.mm"
include "adantr.mm"
include "df-ima.mm"
include "cdm.mm"
include "wrel.mm"
include "freld.mm"
include "resindm.mm"
include "incom.mm"
include "ineq1i.mm"
include "eqtri.mm"
include "fdmd.mm"
include "ineq2d.mm"
include "eleq2i.mm"
include "adantl.mm"
include "uzinico2.mm"
include "3eqtr4d.mm"
include "reseq2d.mm"
include "eqtr3d.mm"
include "rneqd.mm"
include "3eqtrd.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "infeq1d.mm"
include "fveq2.mm"
include "rneqi.mm"
include "infeq1i.mm"

theorem limsupvaluz
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vi: setvar i
  let vn: setvar n
  assume limsupvaluz.m: |- ( ph -> M e. ZZ )
  assume limsupvaluz.z: |- Z = ( ZZ>= ` M )
  assume limsupvaluz.f: |- ( ph -> F : Z --> RR* )

  disjoint F k
  disjoint Z k
  disjoint F i
  disjoint F n
  disjoint i n
  disjoint k n
  disjoint Z i
  disjoint Z n
  disjoint n ph
  assert |- ( ph -> ( limsup ` F ) = inf ( ran ( k e. Z |-> sup ( ran ( F |` ( ZZ>= ` k ) ) , RR* , < ) ) , RR* , < ) )

  proof
    wph
    cF
    clsp
    cfv
    vi
    cr
    cF
    vi
    cv
    #
    cpnf
    cico
    co
    #
    cima
    #
    cxr
    cin
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    cZ
    cima
    #
    cxr
    clt
    cinf
    vn
    cZ
    cF
    vn
    cv
    #
    cuz
    cfv
    #
    cres
    #
    crn
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    cinf
    #
    vk
    cZ
    cF
    vk
    cv
    #
    cuz
    cfv
    #
    cres
    #
    crn
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    cinf
    #
    wph
    cZ
    vi
    cF
    @5
    cvv
    @5
    eqid
    wph
    cF
    cvv
    wph
    cZ
    cxr
    cvv
    cF
    limsupvaluz.f
    cZ
    cvv
    wcel
    wph
    cZ
    cM
    cuz
    cfv
    #
    cvv
    limsupvaluz.z
    cM
    cuz
    fvex
    eqeltri
    a1i
    fexd
    elexd
    cZ
    cr
    wss
    wph
    cZ
    @23
    cr
    limsupvaluz.z
    cM
    uzssre
    eqsstri
    a1i
    #
    wph
    cM
    cz
    wcel
    cZ
    cxr
    clt
    csup
    cpnf
    wceq
    limsupvaluz.m
    cM
    cZ
    limsupvaluz.z
    uzsup
    syl
    limsupval2
    wph
    cxr
    @6
    @13
    clt
    wph
    @6
    vi
    cZ
    @4
    cmpt
    #
    crn
    @13
    wph
    vi
    cr
    @4
    cZ
    @24
    mptima2
    wph
    @25
    @12
    wph
    @25
    vn
    cZ
    cF
    @7
    cpnf
    cico
    co
    #
    cima
    #
    cxr
    cin
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    @12
    @25
    @30
    wceq
    wph
    vi
    vn
    cZ
    @4
    @29
    @0
    @7
    wceq
    #
    cxr
    @3
    @28
    clt
    @31
    @2
    @27
    cxr
    @31
    @1
    @26
    cF
    @0
    @7
    cpnf
    cico
    oveq1
    imaeq2d
    ineq1d
    supeq1d
    cbvmptv
    a1i
    wph
    vn
    cZ
    @29
    @11
    wph
    @7
    cZ
    wcel
    #
    wa
    #
    cxr
    @28
    @10
    clt
    @33
    @28
    @27
    cF
    @26
    cres
    #
    crn
    #
    @10
    wph
    @28
    @27
    wceq
    #
    @32
    wph
    @27
    cxr
    wss
    #
    @36
    wph
    cZ
    cxr
    cF
    wf
    @37
    limsupvaluz.f
    cZ
    cxr
    cF
    @26
    fimass
    syl
    @37
    @36
    @27
    cxr
    df-ss
    biimpi
    syl
    adantr
    @27
    @35
    wceq
    @33
    cF
    @26
    df-ima
    a1i
    @33
    @34
    @9
    @33
    cF
    @26
    cF
    cdm
    #
    cin
    #
    cres
    #
    @34
    @9
    wph
    @40
    @34
    wceq
    #
    @32
    wph
    cF
    wrel
    @41
    wph
    cZ
    cxr
    cF
    limsupvaluz.f
    freld
    cF
    @26
    resindm
    syl
    adantr
    @33
    @39
    @8
    cF
    @33
    @26
    cZ
    cin
    #
    @23
    @26
    cin
    #
    @39
    @8
    @42
    @43
    wceq
    @33
    @42
    cZ
    @26
    cin
    @43
    @26
    cZ
    incom
    cZ
    @23
    @26
    limsupvaluz.z
    ineq1i
    eqtri
    a1i
    wph
    @39
    @42
    wceq
    @32
    wph
    @38
    cZ
    @26
    wph
    cZ
    cxr
    cF
    limsupvaluz.f
    fdmd
    ineq2d
    adantr
    @33
    cM
    @7
    @32
    @7
    @23
    wcel
    #
    wph
    @32
    @44
    cZ
    @23
    @7
    limsupvaluz.z
    eleq2i
    biimpi
    adantl
    uzinico2
    3eqtr4d
    reseq2d
    eqtr3d
    rneqd
    3eqtrd
    supeq1d
    mpteq2dva
    eqtrd
    rneqd
    eqtrd
    infeq1d
    @14
    @22
    wceq
    wph
    cxr
    @13
    @21
    clt
    @12
    @20
    vn
    vk
    cZ
    @11
    @19
    @7
    @15
    wceq
    #
    cxr
    @10
    @18
    clt
    @45
    @9
    @17
    @45
    @8
    @16
    cF
    @7
    @15
    cuz
    fveq2
    reseq2d
    rneqd
    supeq1d
    cbvmptv
    rneqi
    infeq1i
    a1i
    3eqtrd
end
