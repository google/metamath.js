include "cv.mm"
include "clgam.mm"
include "cfv.mm"
include "clog.mm"
include "caddc.mm"
include "co.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cof.mm"
include "c1.mm"
include "cseq.mm"
include "cmpt.mm"
include "culm.mm"
include "cc.mm"
include "wcel.mm"
include "lgamgulm2.mm"
include "simprd.mm"
include "cdm.mm"
include "wi.mm"
include "cn.mm"
include "c2.mm"
include "cmul.mm"
include "cexp.mm"
include "cdiv.mm"
include "cpi.mm"
include "cif.mm"
include "eqid.mm"
include "lgamgulmlem6.mm"
include "mpd.mm"
include "wa.mm"
include "crp.mm"
include "nnrpd.mm"
include "adantr.mm"
include "relogcld.mm"
include "pire.mm"
include "a1i.mm"
include "readdcld.mm"
include "simpr.mm"
include "adantrr.mm"
include "simpld.mm"
include "r19.21bi.mm"
include "abscld.mm"
include "cz.mm"
include "cdif.mm"
include "wss.mm"
include "lgamgulmlem1.mm"
include "sselda.mm"
include "eldifad.mm"
include "dmgmn0.mm"
include "logcld.mm"
include "addcld.mm"
include "ad2antrr.mm"
include "cmin.mm"
include "cneg.mm"
include "negcld.mm"
include "abs2difd.mm"
include "absnegd.mm"
include "oveq2d.mm"
include "subnegd.mm"
include "fveq2d.mm"
include "3brtr3d.mm"
include "lesubadd2d.mm"
include "mpbid.mm"
include "absrpcld.mm"
include "recnd.mm"
include "cc0.mm"
include "wne.mm"
include "abslogle.mm"
include "syl2anc.mm"
include "wceq.mm"
include "1rp.mm"
include "relogdiv.mm"
include "sylancr.mm"
include "df-neg.mm"
include "log1.mm"
include "oveq1i.mm"
include "eqtr4i.mm"
include "syl6reqr.mm"
include "cn0.mm"
include "0nn0.mm"
include "fveq2.mm"
include "breq1d.mm"
include "oveq1.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "elrab2.mm"
include "simprbi.mm"
include "adantl.mm"
include "oveq2.mm"
include "rspcv.mm"
include "mpsyl.mm"
include "addid1d.mm"
include "breqtrd.mm"
include "rpreccld.mm"
include "logled.mm"
include "eqbrtrd.mm"
include "absled.mm"
include "mpbir2and.mm"
include "leadd1dd.mm"
include "letrd.mm"
include "simpllr.mm"
include "leadd2dd.mm"
include "ex.mm"
include "ralimdva.mm"
include "impr.mm"
include "breq2.mm"
include "rspcev.mm"
include "rexlimddv.mm"

theorem lgambdd
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cR: class R
  let cU: class U
  let vk: setvar k
  let vm: setvar m
  let cG: class G
  let vr: setvar r
  let vn: setvar n
  let vy: setvar y
  let vt: setvar t
  let cN: class N
  let cA: class A
  let cO: class O
  let cT: class T
  assume lgamgulm.r: |- ( ph -> R e. NN )
  assume lgamgulm.u: |- U = { x e. CC | ( ( abs ` x ) <_ R /\ A. k e. NN0 ( 1 / R ) <_ ( abs ` ( x + k ) ) ) }
  assume lgamgulm.g: |- G = ( m e. NN |-> ( z e. U |-> ( ( z x. ( log ` ( ( m + 1 ) / m ) ) ) - ( log ` ( ( z / m ) + 1 ) ) ) ) )

  disjoint G r
  disjoint k m
  disjoint k r
  disjoint k x
  disjoint k z
  disjoint R k
  disjoint m r
  disjoint m x
  disjoint m z
  disjoint R m
  disjoint r x
  disjoint r z
  disjoint R r
  disjoint x z
  disjoint R x
  disjoint R z
  disjoint U m
  disjoint U r
  disjoint U z
  disjoint m ph
  disjoint ph r
  disjoint ph x
  disjoint ph z
  disjoint n r
  disjoint n y
  disjoint G n
  disjoint r y
  disjoint G y
  disjoint t x
  disjoint t y
  disjoint N t
  disjoint x y
  disjoint N x
  disjoint N y
  disjoint k n
  disjoint k t
  disjoint k y
  disjoint m n
  disjoint m t
  disjoint m y
  disjoint n t
  disjoint n x
  disjoint n z
  disjoint R n
  disjoint r t
  disjoint t z
  disjoint R t
  disjoint y z
  disjoint R y
  disjoint U n
  disjoint U t
  disjoint U y
  disjoint A k
  disjoint A m
  disjoint A t
  disjoint A x
  disjoint A y
  disjoint O n
  disjoint O r
  disjoint O y
  disjoint n ph
  disjoint ph t
  disjoint ph y
  disjoint T n
  disjoint T r
  disjoint T y
  assert |- ( ph -> E. r e. RR A. z e. U ( abs ` ( log_G ` z ) ) <_ r )

  proof
    wph
    vz
    cv
    #
    clgam
    cfv
    #
    @0
    clog
    cfv
    #
    caddc
    co
    #
    cabs
    cfv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vz
    cU
    wral
    #
    @1
    cabs
    cfv
    #
    vr
    cv
    #
    cle
    wbr
    #
    vz
    cU
    wral
    #
    vr
    cr
    wrex
    #
    vy
    cr
    wph
    caddc
    cof
    cG
    c1
    cseq
    #
    vz
    cU
    @3
    cmpt
    cU
    culm
    cfv
    #
    wbr
    #
    @7
    vy
    cr
    wrex
    #
    wph
    @1
    cc
    wcel
    #
    vz
    cU
    wral
    #
    @15
    wph
    vx
    vz
    cR
    cU
    vk
    vm
    cG
    lgamgulm.r
    lgamgulm.u
    lgamgulm.g
    lgamgulm2
    #
    simprd
    wph
    @13
    @14
    cdm
    wcel
    @15
    @16
    wi
    wph
    vx
    vz
    cR
    vm
    cn
    c2
    cR
    cmul
    co
    vm
    cv
    #
    cle
    wbr
    cR
    c2
    cR
    c1
    caddc
    co
    #
    cmul
    co
    @20
    c2
    cexp
    co
    cdiv
    co
    cmul
    co
    cR
    @20
    c1
    caddc
    co
    @20
    cdiv
    co
    clog
    cfv
    cmul
    co
    @21
    @20
    cmul
    co
    clog
    cfv
    cpi
    caddc
    co
    caddc
    co
    cif
    cmpt
    #
    cU
    vk
    vm
    cG
    @3
    vy
    lgamgulm.r
    lgamgulm.u
    lgamgulm.g
    @22
    eqid
    lgamgulmlem6
    simprd
    mpd
    wph
    @5
    cr
    wcel
    #
    @7
    wa
    wa
    cR
    clog
    cfv
    #
    cpi
    caddc
    co
    #
    @5
    caddc
    co
    #
    cr
    wcel
    #
    @8
    @26
    cle
    wbr
    #
    vz
    cU
    wral
    #
    @12
    wph
    @23
    @27
    @7
    wph
    @23
    wa
    #
    @25
    @5
    @30
    @24
    cpi
    @30
    cR
    wph
    cR
    crp
    wcel
    #
    @23
    wph
    cR
    lgamgulm.r
    nnrpd
    adantr
    #
    relogcld
    cpi
    cr
    wcel
    #
    @30
    pire
    a1i
    readdcld
    wph
    @23
    simpr
    readdcld
    #
    adantrr
    wph
    @23
    @7
    @29
    @30
    @6
    @28
    vz
    cU
    @30
    @0
    cU
    wcel
    #
    wa
    #
    @6
    @28
    @36
    @6
    wa
    #
    @8
    @25
    @4
    caddc
    co
    #
    @26
    @36
    @8
    cr
    wcel
    @6
    @36
    @1
    @30
    @17
    vz
    cU
    wph
    @18
    @23
    wph
    @18
    @15
    @19
    simpld
    adantr
    r19.21bi
    #
    abscld
    #
    adantr
    @36
    @38
    cr
    wcel
    @6
    @36
    @25
    @4
    @36
    @24
    cpi
    @36
    cR
    @30
    @31
    @35
    @32
    adantr
    #
    relogcld
    #
    @33
    @36
    pire
    a1i
    #
    readdcld
    #
    @36
    @3
    @36
    @1
    @2
    @39
    @36
    @0
    @36
    @0
    cc
    cz
    cn
    cdif
    #
    @30
    cU
    cc
    @45
    cdif
    #
    @0
    wph
    cU
    @46
    wss
    @23
    wph
    vx
    cR
    cU
    vk
    lgamgulm.r
    lgamgulm.u
    lgamgulmlem1
    adantr
    sselda
    #
    eldifad
    #
    @36
    @0
    @47
    dmgmn0
    #
    logcld
    #
    addcld
    abscld
    #
    readdcld
    #
    adantr
    @30
    @27
    @35
    @6
    @34
    ad2antrr
    @36
    @8
    @38
    cle
    wbr
    @6
    @36
    @8
    @2
    cabs
    cfv
    #
    @4
    caddc
    co
    #
    @38
    @40
    @36
    @53
    @4
    @36
    @2
    @50
    abscld
    #
    @51
    readdcld
    @52
    @36
    @8
    @53
    cmin
    co
    #
    @4
    cle
    wbr
    @8
    @54
    cle
    wbr
    @36
    @8
    @2
    cneg
    #
    cabs
    cfv
    #
    cmin
    co
    @1
    @57
    cmin
    co
    #
    cabs
    cfv
    @56
    @4
    cle
    @36
    @1
    @57
    @39
    @36
    @2
    @50
    negcld
    abs2difd
    @36
    @58
    @53
    @8
    cmin
    @36
    @2
    @50
    absnegd
    oveq2d
    @36
    @59
    @3
    cabs
    @36
    @1
    @2
    @39
    @50
    subnegd
    fveq2d
    3brtr3d
    @36
    @8
    @53
    @4
    @40
    @55
    @51
    lesubadd2d
    mpbid
    @36
    @53
    @25
    @4
    @55
    @44
    @51
    @36
    @53
    @0
    cabs
    cfv
    #
    clog
    cfv
    #
    cabs
    cfv
    #
    cpi
    caddc
    co
    #
    @25
    @55
    @36
    @62
    cpi
    @36
    @61
    @36
    @61
    @36
    @60
    @36
    @0
    @48
    @49
    absrpcld
    #
    relogcld
    #
    recnd
    abscld
    #
    @43
    readdcld
    @44
    @36
    @0
    cc
    wcel
    #
    @0
    cc0
    wne
    @53
    @63
    cle
    wbr
    @48
    @49
    @0
    abslogle
    syl2anc
    @36
    @62
    @24
    cpi
    @66
    @42
    @43
    @36
    @62
    @24
    cle
    wbr
    @24
    cneg
    #
    @61
    cle
    wbr
    @61
    @24
    cle
    wbr
    #
    @36
    @68
    c1
    cR
    cdiv
    co
    #
    clog
    cfv
    #
    @61
    cle
    @36
    @71
    c1
    clog
    cfv
    #
    @24
    cmin
    co
    #
    @68
    @36
    c1
    crp
    wcel
    @31
    @71
    @73
    wceq
    1rp
    @41
    c1
    cR
    relogdiv
    sylancr
    @68
    cc0
    @24
    cmin
    co
    @73
    @24
    df-neg
    @72
    cc0
    @24
    cmin
    log1
    oveq1i
    eqtr4i
    syl6reqr
    @36
    @70
    @60
    cle
    wbr
    @71
    @61
    cle
    wbr
    @36
    @70
    @0
    cc0
    caddc
    co
    #
    cabs
    cfv
    #
    @60
    cle
    cc0
    cn0
    wcel
    @36
    @70
    @0
    vk
    cv
    #
    caddc
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    vk
    cn0
    wral
    #
    @70
    @75
    cle
    wbr
    #
    0nn0
    @36
    @60
    cR
    cle
    wbr
    #
    @80
    @35
    @82
    @80
    wa
    #
    @30
    @35
    @67
    @83
    vx
    cv
    #
    cabs
    cfv
    #
    cR
    cle
    wbr
    #
    @70
    @84
    @76
    caddc
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    vk
    cn0
    wral
    #
    wa
    @83
    vx
    @0
    cc
    cU
    @84
    @0
    wceq
    #
    @86
    @82
    @90
    @80
    @91
    @85
    @60
    cR
    cle
    @84
    @0
    cabs
    fveq2
    breq1d
    @91
    @89
    @79
    vk
    cn0
    @91
    @88
    @78
    @70
    cle
    @91
    @87
    @77
    cabs
    @84
    @0
    @76
    caddc
    oveq1
    fveq2d
    breq2d
    ralbidv
    anbi12d
    lgamgulm.u
    elrab2
    simprbi
    adantl
    #
    simprd
    @79
    @81
    vk
    cc0
    cn0
    @76
    cc0
    wceq
    #
    @78
    @75
    @70
    cle
    @93
    @77
    @74
    cabs
    @76
    cc0
    @0
    caddc
    oveq2
    fveq2d
    breq2d
    rspcv
    mpsyl
    @36
    @74
    @0
    cabs
    @36
    @0
    @48
    addid1d
    fveq2d
    breqtrd
    @36
    @70
    @60
    @36
    cR
    @41
    rpreccld
    @64
    logled
    mpbid
    eqbrtrd
    @36
    @82
    @69
    @36
    @82
    @80
    @92
    simpld
    @36
    @60
    cR
    @64
    @41
    logled
    mpbid
    @36
    @61
    @24
    @65
    @42
    absled
    mpbir2and
    leadd1dd
    letrd
    leadd1dd
    letrd
    adantr
    @37
    @4
    @5
    @25
    @36
    @4
    cr
    wcel
    @6
    @51
    adantr
    wph
    @23
    @35
    @6
    simpllr
    @36
    @25
    cr
    wcel
    @6
    @44
    adantr
    @36
    @6
    simpr
    leadd2dd
    letrd
    ex
    ralimdva
    impr
    @11
    @29
    vr
    @26
    cr
    @9
    @26
    wceq
    @10
    @28
    vz
    cU
    @9
    @26
    @8
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    rexlimddv
end
