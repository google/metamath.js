include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "ccnv.mm"
include "cmnf.mm"
include "cioc.mm"
include "co.mm"
include "cima.mm"
include "cdm.mm"
include "cin.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "crest.mm"
include "wcel.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "csalgen.mm"
include "nfcv.mm"
include "eqid.mm"
include "cxr.mm"
include "mnfxr.mm"
include "a1i.mm"
include "iocborel.mm"
include "smfpimcc.mm"
include "cz.mm"
include "adantr.mm"
include "csalg.mm"
include "csmblfn.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "wrex.mm"
include "ciin.mm"
include "crab.mm"
include "fveq2.mm"
include "dmeqd.mm"
include "cbviinv.mm"
include "breq1d.mm"
include "ralbidv.mm"
include "wb.mm"
include "fveq1d.mm"
include "cbvralv.mm"
include "bitrd.mm"
include "rexbidv.mm"
include "cbvrabv2.mm"
include "eqtri.mm"
include "cmpt.mm"
include "clt.mm"
include "csup.mm"
include "mpteq2dv.mm"
include "cbvmptv.mm"
include "eqtrd.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "simprl.mm"
include "simplrr.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "ineq12d.mm"
include "eqeq12d.mm"
include "rspccva.mm"
include "sylancom.mm"
include "smfsuplem1.mm"
include "ex.mm"
include "exlimdv.mm"
include "mpd.mm"

theorem smfsuplem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cS: class S
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vh: setvar h
  let vm: setvar m
  let vw: setvar w
  let vk: setvar k
  assume smfsuplem2.m: |- ( ph -> M e. ZZ )
  assume smfsuplem2.z: |- Z = ( ZZ>= ` M )
  assume smfsuplem2.s: |- ( ph -> S e. SAlg )
  assume smfsuplem2.f: |- ( ph -> F : Z --> ( SMblFn ` S ) )
  assume smfsuplem2.d: |- D = { x e. |^|_ n e. Z dom ( F ` n ) | E. y e. RR A. n e. Z ( ( F ` n ) ` x ) <_ y }
  assume smfsuplem2.g: |- G = ( x e. D |-> sup ( ran ( n e. Z |-> ( ( F ` n ) ` x ) ) , RR , < ) )
  assume smfsuplem2.8: |- ( ph -> A e. RR )

  disjoint A n
  disjoint A y
  disjoint n y
  disjoint D y
  disjoint D x
  disjoint x y
  disjoint F n
  disjoint F y
  disjoint F x
  disjoint n x
  disjoint S y
  disjoint Z n
  disjoint Z y
  disjoint Z x
  disjoint ph y
  disjoint A h
  disjoint A m
  disjoint A w
  disjoint h m
  disjoint h n
  disjoint h w
  disjoint h y
  disjoint m n
  disjoint m w
  disjoint m y
  disjoint n w
  disjoint w y
  disjoint D h
  disjoint D m
  disjoint D w
  disjoint m x
  disjoint w x
  disjoint F h
  disjoint F m
  disjoint F w
  disjoint G h
  disjoint G m
  disjoint G w
  disjoint M m
  disjoint S h
  disjoint S m
  disjoint S w
  disjoint Z h
  disjoint Z m
  disjoint Z w
  disjoint h ph
  disjoint m ph
  disjoint ph w
  disjoint k x
  assert |- ( ph -> ( `' G " ( -oo (,] A ) ) e. ( S |`t D ) )

  proof
    wph
    cZ
    cS
    vh
    cv
    #
    wf
    #
    vn
    cv
    #
    cF
    cfv
    #
    ccnv
    #
    cmnf
    cA
    cioc
    co
    #
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
    vn
    cZ
    wral
    #
    wa
    #
    vh
    wex
    cG
    ccnv
    @5
    cima
    cS
    cD
    crest
    co
    wcel
    #
    wph
    @5
    cioo
    crn
    ctg
    cfv
    #
    csalgen
    cfv
    #
    cS
    vh
    vn
    cF
    @14
    cM
    cZ
    vn
    cF
    nfcv
    smfsuplem2.z
    smfsuplem2.s
    smfsuplem2.f
    @14
    eqid
    #
    @15
    eqid
    #
    wph
    cmnf
    @15
    cA
    @14
    cmnf
    cxr
    wcel
    wph
    mnfxr
    a1i
    smfsuplem2.8
    @16
    @17
    iocborel
    smfpimcc
    wph
    @12
    @13
    vh
    wph
    @12
    @13
    wph
    @12
    wa
    #
    vw
    vy
    cA
    cD
    cS
    vm
    cF
    cG
    @0
    cM
    cZ
    wph
    cM
    cz
    wcel
    @12
    smfsuplem2.m
    adantr
    smfsuplem2.z
    wph
    cS
    csalg
    wcel
    @12
    smfsuplem2.s
    adantr
    wph
    cZ
    cS
    csmblfn
    cfv
    cF
    wf
    @12
    smfsuplem2.f
    adantr
    cD
    vx
    cv
    #
    @3
    cfv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vn
    cZ
    wral
    #
    vy
    cr
    wrex
    #
    vx
    vn
    cZ
    @8
    ciin
    #
    crab
    vw
    cv
    #
    vm
    cv
    #
    cF
    cfv
    #
    cfv
    #
    @21
    cle
    wbr
    #
    vm
    cZ
    wral
    #
    vy
    cr
    wrex
    #
    vw
    vm
    cZ
    @28
    cdm
    #
    ciin
    #
    crab
    smfsuplem2.d
    @24
    @32
    vx
    vw
    @25
    @34
    @25
    @34
    wceq
    @19
    @26
    wceq
    #
    vn
    vm
    cZ
    @8
    @33
    @2
    @27
    wceq
    #
    @3
    @28
    @2
    @27
    cF
    fveq2
    #
    dmeqd
    #
    cbviinv
    a1i
    @35
    @23
    @31
    vy
    cr
    @35
    @23
    @26
    @3
    cfv
    #
    @21
    cle
    wbr
    #
    vn
    cZ
    wral
    #
    @31
    @35
    @22
    @40
    vn
    cZ
    @35
    @20
    @39
    @21
    cle
    @19
    @26
    @3
    fveq2
    #
    breq1d
    ralbidv
    @41
    @31
    wb
    @35
    @40
    @30
    vn
    vm
    cZ
    @36
    @39
    @29
    @21
    cle
    @36
    @26
    @3
    @28
    @37
    fveq1d
    #
    breq1d
    cbvralv
    a1i
    bitrd
    rexbidv
    cbvrabv2
    eqtri
    cG
    vx
    cD
    vn
    cZ
    @20
    cmpt
    #
    crn
    #
    cr
    clt
    csup
    #
    cmpt
    vw
    cD
    vm
    cZ
    @29
    cmpt
    #
    crn
    #
    cr
    clt
    csup
    #
    cmpt
    smfsuplem2.g
    vx
    vw
    cD
    @46
    @49
    @35
    cr
    @45
    @48
    clt
    @35
    @44
    @47
    @35
    @44
    vn
    cZ
    @39
    cmpt
    #
    @47
    @35
    vn
    cZ
    @20
    @39
    @42
    mpteq2dv
    @50
    @47
    wceq
    @35
    vn
    vm
    cZ
    @39
    @29
    @43
    cbvmptv
    a1i
    eqtrd
    rneqd
    supeq1d
    cbvmptv
    eqtri
    wph
    cA
    cr
    wcel
    @12
    smfsuplem2.8
    adantr
    wph
    @1
    @11
    simprl
    @18
    @27
    cZ
    wcel
    #
    @11
    @28
    ccnv
    #
    @5
    cima
    #
    @27
    @0
    cfv
    #
    @33
    cin
    #
    wceq
    #
    wph
    @1
    @11
    @51
    simplrr
    @10
    @56
    vn
    @27
    cZ
    @36
    @6
    @53
    @9
    @55
    @36
    @4
    @52
    @5
    @36
    @3
    @28
    @37
    cnveqd
    imaeq1d
    @36
    @7
    @54
    @8
    @33
    @2
    @27
    @0
    fveq2
    @38
    ineq12d
    eqeq12d
    rspccva
    sylancom
    smfsuplem1
    ex
    exlimdv
    mpd
end
