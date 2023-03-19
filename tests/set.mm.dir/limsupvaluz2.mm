include "clsp.mm"
include "cfv.mm"
include "cv.mm"
include "cuz.mm"
include "cres.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cmpt.mm"
include "cinf.mm"
include "cr.mm"
include "frexr.mm"
include "limsupvaluz.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "adantr.mm"
include "id.mm"
include "uzssd2.mm"
include "adantl.mm"
include "feqresmpt.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "nfcv.mm"
include "renepnfd.mm"
include "limsupubuz.mm"
include "wi.mm"
include "ssralv.mm"
include "syl.mm"
include "reximdv.mm"
include "mpd.mm"
include "nfv.mm"
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
include "frnd.mm"
include "cvv.mm"
include "elexd.mm"
include "uzn0d.mm"
include "rnmptn0.mm"
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
include "rnresss.mm"
include "a1i.mm"
include "sstrd.mm"
include "ressxr.mm"
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
include "syl2anc.mm"
include "simp3.mm"
include "fnfvelrn.mm"
include "supxrubd.mm"
include "xrletrd.mm"
include "ex.mm"
include "rexlimdva.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "idi.mm"
include "fveq2.mm"
include "reseq2d.mm"
include "eqcom.mm"
include "imbi1i.mm"
include "imbi2i.mm"
include "bitri.mm"
include "mpbi.mm"
include "breq2d.mm"
include "cbvralv.mm"
include "rexbii.mm"
include "sylib.mm"
include "rnmptbd2.mm"
include "infxrre.mm"
include "syl3anc.mm"
include "cbvmptv.mm"
include "rneqi.mm"
include "infeq1i.mm"
include "3eqtrd.mm"

theorem limsupvaluz2
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
  assume limsupvaluz2.m: |- ( ph -> M e. ZZ )
  assume limsupvaluz2.z: |- Z = ( ZZ>= ` M )
  assume limsupvaluz2.f: |- ( ph -> F : Z --> RR )
  assume limsupvaluz2.r: |- ( ph -> ( limsup ` F ) e. RR )

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
  disjoint n y
  disjoint x y
  disjoint M x
  disjoint Z i
  disjoint Z j
  disjoint Z x
  disjoint Z n
  disjoint Z m
  disjoint Z y
  disjoint i n
  disjoint i ph
  disjoint n ph
  disjoint ph x
  disjoint j ph
  disjoint m ph
  assert |- ( ph -> ( limsup ` F ) = inf ( ran ( k e. Z |-> sup ( ran ( F |` ( ZZ>= ` k ) ) , RR* , < ) ) , RR , < ) )

  proof
    wph
    cF
    clsp
    cfv
    #
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
    @7
    cr
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
    cr
    clt
    cinf
    #
    wph
    vn
    cF
    cM
    cZ
    limsupvaluz2.m
    limsupvaluz2.z
    wph
    cZ
    cF
    limsupvaluz2.f
    frexr
    #
    limsupvaluz
    wph
    @7
    cr
    wss
    @7
    c0
    wne
    vx
    cv
    #
    vy
    cv
    cle
    wbr
    vy
    @7
    wral
    vx
    cr
    wrex
    #
    @8
    @9
    wceq
    wph
    cZ
    cr
    @6
    wph
    vn
    cZ
    @5
    cr
    @6
    wph
    @1
    cZ
    wcel
    #
    wa
    #
    @5
    vm
    @2
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
    @22
    cxr
    @4
    @26
    clt
    @22
    @3
    @25
    @22
    vm
    cZ
    cr
    @2
    cF
    wph
    cZ
    cr
    cF
    wf
    #
    @21
    limsupvaluz2.f
    adantr
    #
    @21
    @2
    cZ
    wss
    #
    wph
    @21
    cM
    @1
    cZ
    limsupvaluz2.z
    @21
    id
    uzssd2
    #
    adantl
    #
    feqresmpt
    rneqd
    supeq1d
    @22
    @27
    cr
    wcel
    @24
    @19
    cle
    wbr
    #
    vm
    @2
    wral
    #
    vx
    cr
    wrex
    #
    @22
    @33
    vm
    cZ
    wral
    #
    vx
    cr
    wrex
    #
    @35
    wph
    @37
    @21
    wph
    vx
    vm
    cF
    cM
    cZ
    vm
    cF
    nfcv
    limsupvaluz2.z
    limsupvaluz2.f
    wph
    @0
    limsupvaluz2.r
    renepnfd
    limsupubuz
    adantr
    @22
    @36
    @34
    vx
    cr
    @21
    @36
    @34
    wi
    #
    wph
    @21
    @30
    @38
    @31
    @33
    vm
    @2
    cZ
    ssralv
    syl
    adantl
    reximdv
    mpd
    @22
    vm
    vx
    @2
    @24
    @22
    vm
    nfv
    @21
    @2
    c0
    wne
    #
    wph
    @21
    @1
    cz
    wcel
    @1
    @2
    wcel
    @39
    cM
    @1
    cZ
    limsupvaluz2.z
    eluzelz2
    @1
    uzid
    @2
    @1
    ne0i
    3syl
    adantl
    @22
    @23
    @2
    wcel
    #
    wa
    cZ
    cr
    @23
    cF
    @22
    @28
    @40
    @29
    adantr
    @22
    @2
    cZ
    @23
    @32
    sselda
    ffvelrnd
    supxrre3rnmpt
    mpbird
    eqeltrd
    #
    @6
    eqid
    #
    fmptd
    frnd
    wph
    vn
    cZ
    @5
    @6
    cvv
    wph
    vn
    nfv
    #
    @22
    @5
    cr
    @41
    elexd
    #
    @42
    wph
    cM
    cZ
    limsupvaluz2.m
    limsupvaluz2.z
    uzn0d
    rnmptn0
    wph
    @19
    @5
    cle
    wbr
    #
    vn
    cZ
    wral
    #
    vx
    cr
    wrex
    #
    @20
    wph
    @19
    cF
    vi
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
    @47
    wph
    @55
    wi
    wph
    @19
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
    @49
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
    @55
    wph
    @61
    @57
    @19
    cle
    wbr
    vj
    @49
    wral
    vi
    cZ
    wrex
    vx
    cr
    wrex
    #
    wph
    @0
    cr
    wcel
    @61
    @62
    wa
    limsupvaluz2.r
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
    limsupvaluz2.m
    limsupvaluz2.z
    @18
    limsupre3uz
    mpbid
    simpld
    wph
    @60
    @54
    vx
    cr
    wph
    @19
    cr
    wcel
    #
    wa
    #
    @59
    @53
    vi
    cZ
    @64
    @48
    cZ
    wcel
    #
    wa
    #
    @58
    @53
    vj
    @49
    @66
    @56
    @49
    wcel
    #
    wa
    #
    @58
    @53
    @68
    @58
    wa
    #
    @19
    @57
    @52
    @69
    @19
    wph
    @63
    @65
    @67
    @58
    simp-4r
    rexrd
    wph
    @65
    @67
    @57
    cxr
    wcel
    @63
    @58
    wph
    @65
    @67
    w3a
    #
    cZ
    cxr
    @56
    cF
    wph
    @65
    cZ
    cxr
    cF
    wf
    @67
    @18
    3ad2ant1
    @65
    @67
    @56
    cZ
    wcel
    wph
    cM
    @56
    @48
    cZ
    limsupvaluz2.z
    uztrn2
    3adant1
    ffvelrnd
    ad5ant134
    wph
    @65
    @52
    cxr
    wcel
    @63
    @67
    @58
    wph
    @65
    wa
    #
    @51
    @71
    @51
    cr
    cxr
    @71
    @51
    cF
    crn
    #
    cr
    @51
    @72
    wss
    @71
    cF
    @49
    rnresss
    a1i
    wph
    @72
    cr
    wss
    @65
    wph
    cZ
    cr
    cF
    limsupvaluz2.f
    frnd
    adantr
    sstrd
    cr
    cxr
    wss
    @71
    ressxr
    a1i
    sstrd
    #
    supxrcld
    ad5ant13
    @68
    @58
    simpr
    wph
    @65
    @67
    @57
    @52
    cle
    wbr
    @63
    @58
    @70
    @51
    @57
    @52
    wph
    @65
    @51
    cxr
    wss
    @67
    @73
    3adant3
    @70
    @57
    @56
    @50
    cfv
    #
    @51
    @67
    wph
    @57
    @74
    wceq
    @65
    @67
    @74
    @57
    @56
    @49
    cF
    fvres
    eqcomd
    3ad2ant3
    @70
    @50
    @49
    wfn
    #
    @67
    @74
    @51
    wcel
    wph
    @65
    @75
    @67
    @71
    cF
    cZ
    wfn
    #
    @49
    cZ
    wss
    #
    @75
    wph
    @76
    @65
    wph
    cZ
    cr
    cF
    limsupvaluz2.f
    ffnd
    adantr
    @65
    @77
    wph
    @65
    cM
    @48
    cZ
    limsupvaluz2.z
    @65
    id
    uzssd2
    adantl
    cZ
    @49
    cF
    fnssres
    syl2anc
    3adant3
    wph
    @65
    @67
    simp3
    @49
    @56
    @50
    fnfvelrn
    syl2anc
    eqeltrd
    @52
    eqid
    supxrubd
    ad5ant134
    xrletrd
    ex
    rexlimdva
    ralimdva
    reximdva
    mpd
    idi
    @54
    @46
    vx
    cr
    @53
    @45
    vi
    vn
    cZ
    @48
    @1
    wceq
    #
    @52
    @5
    @19
    cle
    @1
    @48
    wceq
    #
    @5
    @52
    wceq
    #
    wi
    #
    @78
    @52
    @5
    wceq
    #
    wi
    #
    @79
    cxr
    @4
    @51
    clt
    @79
    @3
    @50
    @79
    @2
    @49
    cF
    @1
    @48
    cuz
    fveq2
    reseq2d
    rneqd
    supeq1d
    @81
    @78
    @80
    wi
    @83
    @79
    @78
    @80
    @1
    @48
    eqcom
    imbi1i
    @80
    @82
    @78
    @5
    @52
    eqcom
    imbi2i
    bitri
    mpbi
    breq2d
    cbvralv
    rexbii
    sylib
    wph
    vn
    vx
    vy
    cZ
    @5
    cvv
    @43
    @44
    rnmptbd2
    mpbid
    vx
    vy
    @7
    infxrre
    syl3anc
    @9
    @17
    wceq
    wph
    cr
    @7
    @16
    clt
    @6
    @15
    vn
    vk
    cZ
    @5
    @14
    @1
    @10
    wceq
    #
    cxr
    @4
    @13
    clt
    @84
    @3
    @12
    @84
    @2
    @11
    cF
    @1
    @10
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
