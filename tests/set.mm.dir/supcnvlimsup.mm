include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "cres.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cmpt.mm"
include "cr.mm"
include "cinf.mm"
include "cli.mm"
include "wbr.mm"
include "clsp.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "adantr.mm"
include "wss.mm"
include "id.mm"
include "uzssd2.mm"
include "adantl.mm"
include "feqresmpt.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "cle.mm"
include "wral.mm"
include "wrex.mm"
include "nfcv.mm"
include "renepnfd.mm"
include "limsupubuz.mm"
include "wi.mm"
include "ssralv.mm"
include "syl.mm"
include "reximdv.mm"
include "mpd.mm"
include "nfv.mm"
include "c0.mm"
include "wne.mm"
include "cz.mm"
include "eluzelz2.mm"
include "uzid.mm"
include "ne0i.mm"
include "3syl.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "supxrre3rnmpt.mm"
include "mpbird.mm"
include "eqeltrd.mm"
include "eqid.mm"
include "fmptd.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "peano2zd.mm"
include "zred.mm"
include "lep1.mm"
include "eluzd.mm"
include "uzss.mm"
include "ssres2.mm"
include "rnss.mm"
include "rnresss.mm"
include "a1i.mm"
include "frnd.mm"
include "sstrd.mm"
include "ressxr.mm"
include "supxrss.mm"
include "syl2anc.mm"
include "wceq.mm"
include "cvv.mm"
include "eqidd.mm"
include "fveq2.mm"
include "reseq2d.mm"
include "peano2uzs.mm"
include "xrltso.mm"
include "supex.mm"
include "fvmptd.mm"
include "breq12d.mm"
include "frexr.mm"
include "limsupre3uz.mm"
include "mpbid.mm"
include "simpld.mm"
include "simp-4r.mm"
include "rexrd.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "uztrn2.mm"
include "3adant1.mm"
include "ad5ant134.mm"
include "supxrcld.mm"
include "ad5ant13.mm"
include "simpr.mm"
include "3adant3.mm"
include "fvres.mm"
include "eqcomd.mm"
include "3ad2ant3.mm"
include "wfn.mm"
include "ffnd.mm"
include "fnssres.mm"
include "simp3.mm"
include "fnfvelrn.mm"
include "supxrubd.mm"
include "xrletrd.mm"
include "ex.mm"
include "rexlimdva.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "simpl.mm"
include "ralbidva.mm"
include "cbvrexv.mm"
include "sylibr.mm"
include "climinf.mm"
include "cbvmptv.mm"
include "limsupvaluz2.mm"

theorem supcnvlimsup
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vi: setvar i
  let vj: setvar j
  let vx: setvar x
  let vn: setvar n
  let vm: setvar m
  let vy: setvar y
  assume supcnvlimsup.m: |- ( ph -> M e. ZZ )
  assume supcnvlimsup.z: |- Z = ( ZZ>= ` M )
  assume supcnvlimsup.f: |- ( ph -> F : Z --> RR )
  assume supcnvlimsup.r: |- ( ph -> ( limsup ` F ) e. RR )

  disjoint F k
  disjoint Z k
  disjoint F i
  disjoint F j
  disjoint F x
  disjoint i j
  disjoint i x
  disjoint j x
  disjoint F n
  disjoint k n
  disjoint F m
  disjoint m n
  disjoint m x
  disjoint n x
  disjoint F y
  disjoint i n
  disjoint i y
  disjoint n y
  disjoint x y
  disjoint M x
  disjoint Z i
  disjoint Z j
  disjoint Z x
  disjoint Z n
  disjoint Z m
  disjoint Z y
  disjoint i ph
  disjoint j ph
  disjoint ph x
  disjoint m ph
  disjoint n ph
  assert |- ( ph -> ( k e. Z |-> sup ( ran ( F |` ( ZZ>= ` k ) ) , RR* , < ) ) ~~> ( limsup ` F ) )

  proof
    wph
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
    @5
    crn
    cr
    clt
    cinf
    #
    cli
    wbr
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
    cF
    clsp
    cfv
    #
    cli
    wbr
    wph
    vy
    vi
    @5
    cM
    cZ
    supcnvlimsup.z
    supcnvlimsup.m
    wph
    vn
    cZ
    @4
    cr
    @5
    wph
    @0
    cZ
    wcel
    #
    wa
    #
    @4
    vm
    @1
    vm
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cr
    @15
    cxr
    @3
    @19
    clt
    @15
    @2
    @18
    @15
    vm
    cZ
    cr
    @1
    cF
    wph
    cZ
    cr
    cF
    wf
    #
    @14
    supcnvlimsup.f
    adantr
    #
    @14
    @1
    cZ
    wss
    #
    wph
    @14
    cM
    @0
    cZ
    supcnvlimsup.z
    @14
    id
    uzssd2
    #
    adantl
    #
    feqresmpt
    rneqd
    supeq1d
    @15
    @20
    cr
    wcel
    @17
    vx
    cv
    #
    cle
    wbr
    #
    vm
    @1
    wral
    #
    vx
    cr
    wrex
    #
    @15
    @27
    vm
    cZ
    wral
    #
    vx
    cr
    wrex
    #
    @29
    wph
    @31
    @14
    wph
    vx
    vm
    cF
    cM
    cZ
    vm
    cF
    nfcv
    supcnvlimsup.z
    supcnvlimsup.f
    wph
    @13
    supcnvlimsup.r
    renepnfd
    limsupubuz
    adantr
    @15
    @30
    @28
    vx
    cr
    @14
    @30
    @28
    wi
    #
    wph
    @14
    @23
    @32
    @24
    @27
    vm
    @1
    cZ
    ssralv
    syl
    adantl
    reximdv
    mpd
    @15
    vm
    vx
    @1
    @17
    @15
    vm
    nfv
    @14
    @1
    c0
    wne
    #
    wph
    @14
    @0
    cz
    wcel
    @0
    @1
    wcel
    @33
    cM
    @0
    cZ
    supcnvlimsup.z
    eluzelz2
    @0
    uzid
    @1
    @0
    ne0i
    3syl
    adantl
    @15
    @16
    @1
    wcel
    #
    wa
    cZ
    cr
    @16
    cF
    @15
    @21
    @34
    @22
    adantr
    @15
    @1
    cZ
    @16
    @25
    sselda
    ffvelrnd
    supxrre3rnmpt
    mpbird
    eqeltrd
    @5
    eqid
    fmptd
    wph
    vi
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @35
    c1
    caddc
    co
    #
    @5
    cfv
    #
    @35
    @5
    cfv
    #
    cle
    wbr
    cF
    @38
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
    cF
    @35
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
    cle
    wbr
    #
    @37
    @43
    @47
    wss
    #
    @47
    cxr
    wss
    #
    @49
    @36
    @50
    wph
    @36
    @42
    @46
    wss
    #
    @50
    @36
    @41
    @45
    wss
    #
    @52
    @36
    @38
    @45
    wcel
    @53
    @36
    @35
    @38
    @45
    @45
    eqid
    cM
    @35
    cZ
    supcnvlimsup.z
    eluzelz2
    #
    @36
    @35
    @54
    peano2zd
    @36
    @35
    cr
    wcel
    @35
    @38
    cle
    wbr
    @36
    @35
    @54
    zred
    @35
    lep1
    syl
    eluzd
    @35
    @38
    uzss
    syl
    @41
    @45
    cF
    ssres2
    syl
    @42
    @46
    rnss
    syl
    adantl
    @37
    @47
    cr
    cxr
    @37
    @47
    cF
    crn
    #
    cr
    @47
    @55
    wss
    @37
    cF
    @45
    rnresss
    a1i
    wph
    @55
    cr
    wss
    @36
    wph
    cZ
    cr
    cF
    supcnvlimsup.f
    frnd
    adantr
    sstrd
    cr
    cxr
    wss
    @37
    ressxr
    a1i
    sstrd
    #
    @43
    @47
    supxrss
    syl2anc
    @37
    @39
    @44
    @40
    @48
    cle
    @36
    @39
    @44
    wceq
    wph
    @36
    vn
    @38
    @4
    @44
    cZ
    @5
    cvv
    @36
    @5
    eqidd
    #
    @0
    @38
    wceq
    #
    @4
    @44
    wceq
    @36
    @58
    cxr
    @3
    @43
    clt
    @58
    @2
    @42
    @58
    @1
    @41
    cF
    @0
    @38
    cuz
    fveq2
    reseq2d
    rneqd
    supeq1d
    adantl
    cM
    @35
    cZ
    supcnvlimsup.z
    peano2uzs
    @44
    cvv
    wcel
    @36
    cxr
    @43
    clt
    xrltso
    supex
    a1i
    fvmptd
    adantl
    @36
    @40
    @48
    wceq
    #
    wph
    @36
    vn
    @35
    @4
    @48
    cZ
    @5
    cvv
    @57
    @0
    @35
    wceq
    #
    @4
    @48
    wceq
    @36
    @60
    cxr
    @3
    @47
    clt
    @60
    @2
    @46
    @60
    @1
    @45
    cF
    @0
    @35
    cuz
    fveq2
    reseq2d
    rneqd
    supeq1d
    adantl
    @36
    id
    #
    @48
    cvv
    wcel
    @36
    cxr
    @47
    clt
    xrltso
    supex
    a1i
    fvmptd
    #
    adantl
    breq12d
    mpbird
    wph
    @26
    @48
    cle
    wbr
    #
    vi
    cZ
    wral
    #
    vx
    cr
    wrex
    #
    vy
    cv
    #
    @40
    cle
    wbr
    #
    vi
    cZ
    wral
    #
    vy
    cr
    wrex
    wph
    @26
    vj
    cv
    #
    cF
    cfv
    #
    cle
    wbr
    #
    vj
    @45
    wrex
    #
    vi
    cZ
    wral
    #
    vx
    cr
    wrex
    #
    @65
    wph
    @74
    @70
    @26
    cle
    wbr
    vj
    @45
    wral
    vi
    cZ
    wrex
    vx
    cr
    wrex
    #
    wph
    @13
    cr
    wcel
    @74
    @75
    wa
    supcnvlimsup.r
    wph
    vx
    vj
    vi
    cF
    cM
    cZ
    vj
    cF
    nfcv
    supcnvlimsup.m
    supcnvlimsup.z
    wph
    cZ
    cF
    supcnvlimsup.f
    frexr
    #
    limsupre3uz
    mpbid
    simpld
    wph
    @73
    @64
    vx
    cr
    wph
    @26
    cr
    wcel
    #
    wa
    #
    @72
    @63
    vi
    cZ
    @78
    @36
    wa
    #
    @71
    @63
    vj
    @45
    @79
    @69
    @45
    wcel
    #
    wa
    #
    @71
    @63
    @81
    @71
    wa
    #
    @26
    @70
    @48
    @82
    @26
    wph
    @77
    @36
    @80
    @71
    simp-4r
    rexrd
    wph
    @36
    @80
    @70
    cxr
    wcel
    @77
    @71
    wph
    @36
    @80
    w3a
    #
    cZ
    cxr
    @69
    cF
    wph
    @36
    cZ
    cxr
    cF
    wf
    @80
    @76
    3ad2ant1
    @36
    @80
    @69
    cZ
    wcel
    wph
    cM
    @69
    @35
    cZ
    supcnvlimsup.z
    uztrn2
    3adant1
    ffvelrnd
    ad5ant134
    wph
    @36
    @48
    cxr
    wcel
    @77
    @80
    @71
    @37
    @47
    @56
    supxrcld
    ad5ant13
    @81
    @71
    simpr
    wph
    @36
    @80
    @70
    @48
    cle
    wbr
    @77
    @71
    @83
    @47
    @70
    @48
    wph
    @36
    @51
    @80
    @56
    3adant3
    @83
    @70
    @69
    @46
    cfv
    #
    @47
    @80
    wph
    @70
    @84
    wceq
    @36
    @80
    @84
    @70
    @69
    @45
    cF
    fvres
    eqcomd
    3ad2ant3
    @83
    @46
    @45
    wfn
    #
    @80
    @84
    @47
    wcel
    wph
    @36
    @85
    @80
    @37
    cF
    cZ
    wfn
    #
    @45
    cZ
    wss
    #
    @85
    wph
    @86
    @36
    wph
    cZ
    cr
    cF
    supcnvlimsup.f
    ffnd
    adantr
    @36
    @87
    wph
    @36
    cM
    @35
    cZ
    supcnvlimsup.z
    @61
    uzssd2
    adantl
    cZ
    @45
    cF
    fnssres
    syl2anc
    3adant3
    wph
    @36
    @80
    simp3
    @45
    @69
    @46
    fnfvelrn
    syl2anc
    eqeltrd
    @48
    eqid
    supxrubd
    ad5ant134
    xrletrd
    ex
    rexlimdva
    ralimdva
    reximdva
    mpd
    @68
    @64
    vy
    vx
    cr
    @66
    @26
    wceq
    #
    @67
    @63
    vi
    cZ
    @88
    @36
    wa
    @66
    @26
    @40
    @48
    cle
    @88
    @36
    simpl
    @36
    @59
    @88
    @62
    adantl
    breq12d
    ralbidva
    cbvrexv
    sylibr
    climinf
    wph
    @5
    @12
    @6
    @13
    cli
    @5
    @12
    wceq
    wph
    vn
    vk
    cZ
    @4
    @11
    @0
    @7
    wceq
    #
    cxr
    @3
    @10
    clt
    @89
    @2
    @9
    @89
    @1
    @8
    cF
    @0
    @7
    cuz
    fveq2
    reseq2d
    rneqd
    supeq1d
    cbvmptv
    a1i
    wph
    @13
    @6
    wph
    vn
    cF
    cM
    cZ
    supcnvlimsup.m
    supcnvlimsup.z
    supcnvlimsup.f
    supcnvlimsup.r
    limsupvaluz2
    eqcomd
    breq12d
    mpbid
end
