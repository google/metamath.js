include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "cuz.mm"
include "ciin.mm"
include "ciun.mm"
include "crab.mm"
include "csmblfn.mm"
include "clsp.mm"
include "wceq.mm"
include "a1i.mm"
include "smflimsuplem7.mm"
include "wa.mm"
include "wrex.mm"
include "cr.mm"
include "rabidim1.mm"
include "eliun.mm"
include "sylib.mm"
include "eleq2s.mm"
include "adantl.mm"
include "nfv.mm"
include "w3a.mm"
include "wbr.mm"
include "nfcv.mm"
include "nfii1.mm"
include "nfel.mm"
include "nf3an.mm"
include "cz.mm"
include "adantr.mm"
include "3ad2ant1.mm"
include "csalg.mm"
include "wf.mm"
include "rabidim2.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "cbvmptv.mm"
include "3eqtr2i.mm"
include "fveq2i.mm"
include "eleq1i.mm"
include "sylibr.mm"
include "simp2.mm"
include "simp3.mm"
include "smflimsuplem5.mm"
include "cvv.mm"
include "fvexd.mm"
include "fvexi.mm"
include "eluzelz2d.mm"
include "eqid.mm"
include "uzidd.mm"
include "uzssd.mm"
include "uzssd2.mm"
include "climeqmpt.mm"
include "mpbid.mm"
include "simp1l.mm"
include "nfan.mm"
include "eluzelz2.mm"
include "limsupequzmpt.mm"
include "syl2anc.mm"
include "breqtrd.mm"
include "climfvd.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"
include "mpteq12dva.mm"
include "eqtrd.mm"
include "smflimsuplem3.mm"
include "eqeltrd.mm"

theorem smflimsuplem8
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let cS: class S
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cZ: class Z
  let vw: setvar w
  let vz: setvar z
  let vy: setvar y
  assume smflimsuplem8.m: |- ( ph -> M e. ZZ )
  assume smflimsuplem8.z: |- Z = ( ZZ>= ` M )
  assume smflimsuplem8.s: |- ( ph -> S e. SAlg )
  assume smflimsuplem8.f: |- ( ph -> F : Z --> ( SMblFn ` S ) )
  assume smflimsuplem8.d: |- D = { x e. U_ n e. Z |^|_ m e. ( ZZ>= ` n ) dom ( F ` m ) | ( limsup ` ( m e. Z |-> ( ( F ` m ) ` x ) ) ) e. RR }
  assume smflimsuplem8.g: |- G = ( x e. D |-> ( limsup ` ( m e. Z |-> ( ( F ` m ) ` x ) ) ) )
  assume smflimsuplem8.e: |- E = ( k e. Z |-> { x e. |^|_ m e. ( ZZ>= ` k ) dom ( F ` m ) | sup ( ran ( m e. ( ZZ>= ` k ) |-> ( ( F ` m ) ` x ) ) , RR* , < ) e. RR } )
  assume smflimsuplem8.h: |- H = ( k e. Z |-> ( x e. ( E ` k ) |-> sup ( ran ( m e. ( ZZ>= ` k ) |-> ( ( F ` m ) ` x ) ) , RR* , < ) ) )

  disjoint D k
  disjoint D m
  disjoint D n
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint E k
  disjoint E x
  disjoint k x
  disjoint F k
  disjoint F m
  disjoint F n
  disjoint F x
  disjoint m x
  disjoint n x
  disjoint H k
  disjoint H m
  disjoint H n
  disjoint H x
  disjoint M m
  disjoint S k
  disjoint S n
  disjoint Z k
  disjoint Z m
  disjoint Z n
  disjoint Z x
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint k x
  disjoint F w
  disjoint F z
  disjoint w x
  disjoint w z
  disjoint x z
  disjoint F y
  disjoint m y
  disjoint x y
  disjoint Z w
  disjoint Z z
  disjoint Z y
  disjoint y z
  assert |- ( ph -> G e. ( SMblFn ` S ) )

  proof
    wph
    cG
    vx
    vk
    cZ
    vx
    cv
    #
    vk
    cv
    #
    cH
    cfv
    #
    cfv
    #
    cmpt
    #
    cli
    cdm
    wcel
    vx
    vn
    cZ
    vk
    vn
    cv
    #
    cuz
    cfv
    #
    @2
    cdm
    ciin
    ciun
    crab
    #
    @4
    cli
    cfv
    #
    cmpt
    #
    cS
    csmblfn
    cfv
    #
    wph
    cG
    vx
    cD
    vm
    cZ
    @0
    vm
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmpt
    #
    clsp
    cfv
    #
    cmpt
    #
    @9
    cG
    @16
    wceq
    wph
    smflimsuplem8.g
    a1i
    wph
    vx
    cD
    @15
    @7
    @8
    wph
    vx
    cD
    cS
    vk
    vm
    vn
    cE
    cF
    cH
    cM
    cZ
    smflimsuplem8.m
    smflimsuplem8.z
    smflimsuplem8.s
    smflimsuplem8.f
    smflimsuplem8.d
    smflimsuplem8.e
    smflimsuplem8.h
    smflimsuplem7
    wph
    @0
    cD
    wcel
    #
    wa
    #
    @0
    vm
    @6
    @12
    cdm
    #
    ciin
    #
    wcel
    #
    vn
    cZ
    wrex
    #
    @15
    @8
    wceq
    #
    @17
    @22
    wph
    @22
    @0
    @15
    cr
    wcel
    #
    vx
    vn
    cZ
    @20
    ciun
    #
    crab
    #
    cD
    @0
    @26
    wcel
    @0
    @25
    wcel
    @22
    @24
    vx
    @25
    rabidim1
    vn
    @0
    cZ
    @20
    eliun
    sylib
    smflimsuplem8.d
    eleq2s
    adantl
    @18
    @21
    @23
    vn
    cZ
    @18
    vn
    nfv
    @23
    vn
    nfv
    @18
    @5
    cZ
    wcel
    #
    @21
    @23
    @18
    @27
    @21
    w3a
    #
    @15
    @4
    @28
    @4
    vm
    @6
    @13
    cmpt
    clsp
    cfv
    #
    @15
    cli
    @28
    vk
    @6
    @3
    cmpt
    @29
    cli
    wbr
    @4
    @29
    cli
    wbr
    @28
    vx
    cS
    vm
    vk
    cE
    cF
    cH
    cM
    @5
    @0
    cZ
    @28
    vk
    nfv
    #
    @18
    @27
    @21
    vm
    @18
    vm
    nfv
    @27
    vm
    nfv
    #
    vm
    @0
    @20
    vm
    @0
    nfcv
    vm
    @6
    @19
    nfii1
    nfel
    nf3an
    @18
    @27
    cM
    cz
    wcel
    #
    @21
    wph
    @32
    @17
    smflimsuplem8.m
    adantr
    3ad2ant1
    smflimsuplem8.z
    @18
    @27
    cS
    csalg
    wcel
    #
    @21
    wph
    @33
    @17
    smflimsuplem8.s
    adantr
    3ad2ant1
    @18
    @27
    cZ
    @10
    cF
    wf
    #
    @21
    wph
    @34
    @17
    smflimsuplem8.f
    adantr
    3ad2ant1
    smflimsuplem8.e
    smflimsuplem8.h
    @28
    vw
    cZ
    @0
    vw
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmpt
    #
    clsp
    cfv
    #
    cr
    wcel
    #
    @24
    @18
    @27
    @40
    @21
    @17
    @40
    wph
    @17
    @24
    @40
    @24
    @0
    @26
    cD
    @24
    vx
    @25
    rabidim2
    smflimsuplem8.d
    eleq2s
    @15
    @39
    cr
    @14
    @38
    clsp
    @14
    vy
    cZ
    @0
    vy
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmpt
    vz
    cZ
    @0
    vz
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmpt
    @38
    vm
    vy
    cZ
    @13
    @43
    @11
    @41
    wceq
    @0
    @12
    @42
    @11
    @41
    cF
    fveq2
    fveq1d
    cbvmptv
    vz
    vy
    cZ
    @46
    @43
    @44
    @41
    wceq
    @0
    @45
    @42
    @44
    @41
    cF
    fveq2
    fveq1d
    cbvmptv
    vz
    vw
    cZ
    @46
    @37
    @44
    @35
    wceq
    @0
    @45
    @36
    @44
    @35
    cF
    fveq2
    fveq1d
    cbvmptv
    3eqtr2i
    fveq2i
    eleq1i
    #
    sylib
    adantl
    3ad2ant1
    @47
    sylibr
    @18
    @27
    @21
    simp2
    #
    @18
    @27
    @21
    simp3
    smflimsuplem5
    @28
    vk
    @6
    cZ
    @3
    @29
    cvv
    @5
    cvv
    cvv
    @6
    @30
    @28
    @5
    cuz
    fvexd
    cZ
    cvv
    wcel
    @28
    cZ
    cM
    cuz
    smflimsuplem8.z
    fvexi
    a1i
    @28
    cM
    @5
    cZ
    smflimsuplem8.z
    @48
    eluzelz2d
    #
    @6
    eqid
    #
    @28
    @5
    @5
    @28
    @5
    @49
    uzidd
    uzssd
    @28
    cM
    @5
    cZ
    smflimsuplem8.z
    @48
    uzssd2
    @28
    @1
    @6
    wcel
    wa
    @0
    @2
    fvexd
    climeqmpt
    mpbid
    @28
    wph
    @27
    @29
    @15
    wceq
    wph
    @17
    @27
    @21
    simp1l
    @48
    wph
    @27
    wa
    #
    @6
    cZ
    @13
    vm
    @5
    cM
    cvv
    cvv
    wph
    @27
    vm
    wph
    vm
    nfv
    @31
    nfan
    @27
    @5
    cz
    wcel
    wph
    cM
    @5
    cZ
    smflimsuplem8.z
    eluzelz2
    adantl
    wph
    @32
    @27
    smflimsuplem8.m
    adantr
    @50
    smflimsuplem8.z
    @51
    @11
    @6
    wcel
    wa
    @0
    @12
    fvexd
    @51
    @11
    cZ
    wcel
    wa
    @0
    @12
    fvexd
    limsupequzmpt
    syl2anc
    breqtrd
    climfvd
    3exp
    rexlimd
    mpd
    mpteq12dva
    eqtrd
    wph
    vx
    cS
    vn
    vm
    vk
    cE
    cF
    cH
    cM
    cZ
    smflimsuplem8.m
    smflimsuplem8.z
    smflimsuplem8.s
    smflimsuplem8.f
    smflimsuplem8.e
    smflimsuplem8.h
    smflimsuplem3
    eqeltrd
end
