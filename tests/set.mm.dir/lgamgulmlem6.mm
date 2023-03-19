include "caddc.mm"
include "cof.mm"
include "c1.mm"
include "cseq.mm"
include "culm.mm"
include "cfv.mm"
include "cdm.mm"
include "wcel.mm"
include "cmpt.mm"
include "wbr.mm"
include "cabs.mm"
include "cv.mm"
include "cle.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "wi.mm"
include "cvv.mm"
include "cn.mm"
include "nnuz.mm"
include "1zzd.mm"
include "cdiv.mm"
include "co.mm"
include "cn0.mm"
include "wa.mm"
include "cc.mm"
include "cnex.mm"
include "rabex2.mm"
include "a1i.mm"
include "clog.mm"
include "cmul.mm"
include "cmin.mm"
include "cmap.mm"
include "wf.mm"
include "cz.mm"
include "cdif.mm"
include "wss.mm"
include "lgamgulmlem1.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "sseldd.mm"
include "eldifad.mm"
include "simplr.mm"
include "peano2nnd.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "relogcld.mm"
include "recnd.mm"
include "mulcld.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcld.mm"
include "1cnd.mm"
include "addcld.mm"
include "dmgmdivn0.mm"
include "logcld.mm"
include "subcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "elmap.mm"
include "sylibr.mm"
include "c2.mm"
include "cexp.mm"
include "cpi.mm"
include "cif.mm"
include "nnex.mm"
include "mptex.mm"
include "eqeltri.mm"
include "adantr.mm"
include "nnred.mm"
include "2re.mm"
include "1red.mm"
include "readdcld.mm"
include "remulcld.mm"
include "nnsqcld.mm"
include "nndivred.mm"
include "rpmulcld.mm"
include "pire.mm"
include "ifcld.mm"
include "ffvelrnda.mm"
include "lgamgulmlem5.mm"
include "lgamgulmlem4.mm"
include "mtest.mm"
include "adantlr.mm"
include "cli.mm"
include "mtestbdd.mm"
include "nfcv.mm"
include "nffvmpt1.mm"
include "nffv.mm"
include "nfbr.mm"
include "nfv.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "cbvral.mm"
include "wb.mm"
include "ulmcl.mm"
include "adantl.mm"
include "fmpt.mm"
include "fvmpt2.mm"
include "ralimiaa.mm"
include "ralbi.mm"
include "3syl.mm"
include "syl5bb.mm"
include "rexbidv.mm"
include "mpbid.mm"
include "ex.mm"
include "jca.mm"

theorem lgamgulmlem6
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cR: class R
  let cT: class T
  let cU: class U
  let vk: setvar k
  let vm: setvar m
  let cG: class G
  let cO: class O
  let vr: setvar r
  let vn: setvar n
  let vy: setvar y
  let vt: setvar t
  let cN: class N
  let cA: class A
  assume lgamgulm.r: |- ( ph -> R e. NN )
  assume lgamgulm.u: |- U = { x e. CC | ( ( abs ` x ) <_ R /\ A. k e. NN0 ( 1 / R ) <_ ( abs ` ( x + k ) ) ) }
  assume lgamgulm.g: |- G = ( m e. NN |-> ( z e. U |-> ( ( z x. ( log ` ( ( m + 1 ) / m ) ) ) - ( log ` ( ( z / m ) + 1 ) ) ) ) )
  assume lgamgulm.t: |- T = ( m e. NN |-> if ( ( 2 x. R ) <_ m , ( R x. ( ( 2 x. ( R + 1 ) ) / ( m ^ 2 ) ) ) , ( ( R x. ( log ` ( ( m + 1 ) / m ) ) ) + ( ( log ` ( ( R + 1 ) x. m ) ) + _pi ) ) ) )

  disjoint m ph
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
  disjoint O r
  disjoint m ph
  disjoint ph r
  disjoint ph x
  disjoint ph z
  disjoint T r
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
  disjoint O y
  disjoint n ph
  disjoint ph t
  disjoint ph y
  disjoint T n
  disjoint T y
  assert |- ( ph -> ( seq 1 ( oF + , G ) e. dom ( ~~>u ` U ) /\ ( seq 1 ( oF + , G ) ( ~~>u ` U ) ( z e. U |-> O ) -> E. r e. RR A. z e. U ( abs ` O ) <_ r ) ) )

  proof
    wph
    caddc
    cof
    cG
    c1
    cseq
    #
    cU
    culm
    cfv
    #
    cdm
    wcel
    @0
    vz
    cU
    cO
    cmpt
    #
    @1
    wbr
    #
    cO
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
    wi
    wph
    vy
    cU
    vn
    cG
    cT
    c1
    cvv
    cvv
    cn
    nnuz
    wph
    1zzd
    cU
    cvv
    wcel
    #
    wph
    vx
    cv
    #
    cabs
    cfv
    cR
    cle
    wbr
    c1
    cR
    cdiv
    co
    @10
    vk
    cv
    caddc
    co
    cabs
    cfv
    cle
    wbr
    vk
    cn0
    wral
    wa
    vx
    cc
    cU
    lgamgulm.u
    cnex
    rabex2
    #
    a1i
    wph
    vm
    cn
    vz
    cU
    vz
    cv
    #
    vm
    cv
    #
    c1
    caddc
    co
    #
    @13
    cdiv
    co
    #
    clog
    cfv
    #
    cmul
    co
    #
    @12
    @13
    cdiv
    co
    #
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    cmpt
    #
    cc
    cU
    cmap
    co
    #
    cG
    wph
    @13
    cn
    wcel
    #
    wa
    #
    cU
    cc
    @22
    wf
    @22
    @23
    wcel
    @25
    vz
    cU
    @21
    cc
    @22
    @25
    @12
    cU
    wcel
    #
    wa
    #
    @17
    @20
    @27
    @12
    @16
    @27
    @12
    cc
    cz
    cn
    cdif
    #
    @27
    cU
    cc
    @28
    cdif
    #
    @12
    wph
    cU
    @29
    wss
    @24
    @26
    wph
    vx
    cR
    cU
    vk
    lgamgulm.r
    lgamgulm.u
    lgamgulmlem1
    ad2antrr
    @25
    @26
    simpr
    sseldd
    #
    eldifad
    #
    @27
    @16
    @27
    @15
    @27
    @14
    @13
    @27
    @14
    @27
    @13
    wph
    @24
    @26
    simplr
    #
    peano2nnd
    nnrpd
    @27
    @13
    @32
    nnrpd
    rpdivcld
    relogcld
    recnd
    mulcld
    @27
    @19
    @27
    @18
    c1
    @27
    @12
    @13
    @31
    @27
    @13
    @32
    nncnd
    @27
    @13
    @32
    nnne0d
    divcld
    @27
    1cnd
    addcld
    @27
    @12
    @13
    @30
    @32
    dmgmdivn0
    logcld
    subcld
    @22
    eqid
    fmptd
    cc
    cU
    @22
    cnex
    @11
    elmap
    sylibr
    lgamgulm.g
    fmptd
    #
    cT
    cvv
    wcel
    #
    wph
    cT
    vm
    cn
    c2
    cR
    cmul
    co
    @13
    cle
    wbr
    #
    cR
    c2
    cR
    c1
    caddc
    co
    #
    cmul
    co
    #
    @13
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    cR
    @16
    cmul
    co
    #
    @36
    @13
    cmul
    co
    #
    clog
    cfv
    #
    cpi
    caddc
    co
    #
    caddc
    co
    #
    cif
    #
    cmpt
    cvv
    lgamgulm.t
    vm
    cn
    @46
    nnex
    mptex
    eqeltri
    #
    a1i
    wph
    cn
    cr
    vn
    cv
    #
    cT
    wph
    vm
    cn
    @46
    cr
    cT
    @25
    @35
    @40
    @45
    cr
    @25
    cR
    @39
    @25
    cR
    wph
    cR
    cn
    wcel
    @24
    lgamgulm.r
    adantr
    #
    nnred
    #
    @25
    @37
    @38
    @25
    c2
    @36
    c2
    cr
    wcel
    @25
    2re
    a1i
    @25
    cR
    c1
    @50
    @25
    1red
    readdcld
    remulcld
    @25
    @13
    wph
    @24
    simpr
    #
    nnsqcld
    nndivred
    remulcld
    @25
    @41
    @44
    @25
    cR
    @16
    @50
    @25
    @15
    @25
    @14
    @13
    @25
    @14
    @25
    @13
    @51
    peano2nnd
    nnrpd
    @25
    @13
    @51
    nnrpd
    #
    rpdivcld
    relogcld
    remulcld
    @25
    @43
    cpi
    @25
    @42
    @25
    @36
    @13
    @25
    @36
    @25
    cR
    @49
    peano2nnd
    nnrpd
    @52
    rpmulcld
    relogcld
    cpi
    cr
    wcel
    @25
    pire
    a1i
    readdcld
    readdcld
    ifcld
    lgamgulm.t
    fmptd
    ffvelrnda
    #
    wph
    vx
    vy
    vz
    cR
    cT
    cU
    vk
    vm
    vn
    cG
    lgamgulm.r
    lgamgulm.u
    lgamgulm.g
    lgamgulm.t
    lgamgulmlem5
    #
    wph
    vx
    vz
    cR
    cT
    cU
    vk
    vm
    cG
    lgamgulm.r
    lgamgulm.u
    lgamgulm.g
    lgamgulm.t
    lgamgulmlem4
    #
    mtest
    wph
    @3
    @8
    wph
    @3
    wa
    #
    vy
    cv
    #
    @2
    cfv
    #
    cabs
    cfv
    #
    @5
    cle
    wbr
    #
    vy
    cU
    wral
    #
    vr
    cr
    wrex
    @8
    @56
    vr
    vy
    cU
    @2
    vn
    cG
    cT
    c1
    cvv
    cvv
    cn
    nnuz
    @56
    1zzd
    @9
    @56
    @11
    a1i
    wph
    cn
    @23
    cG
    wf
    @3
    @33
    adantr
    @34
    @56
    @47
    a1i
    wph
    @48
    cn
    wcel
    #
    @48
    cT
    cfv
    #
    cr
    wcel
    @3
    @53
    adantlr
    wph
    @62
    @57
    cU
    wcel
    wa
    @57
    @48
    cG
    cfv
    cfv
    cabs
    cfv
    @63
    cle
    wbr
    @3
    @54
    adantlr
    wph
    caddc
    cT
    c1
    cseq
    cli
    cdm
    wcel
    @3
    @55
    adantr
    wph
    @3
    simpr
    mtestbdd
    @56
    @61
    @7
    vr
    cr
    @61
    @12
    @2
    cfv
    #
    cabs
    cfv
    #
    @5
    cle
    wbr
    #
    vz
    cU
    wral
    #
    @56
    @7
    @60
    @66
    vy
    vz
    cU
    vz
    @59
    @5
    cle
    vz
    @58
    cabs
    vz
    cabs
    nfcv
    vz
    cU
    cO
    @57
    nffvmpt1
    nffv
    vz
    cle
    nfcv
    vz
    @5
    nfcv
    nfbr
    @66
    vy
    nfv
    vy
    vz
    weq
    #
    @59
    @65
    @5
    cle
    @68
    @58
    @64
    cabs
    @57
    @12
    @2
    fveq2
    fveq2d
    breq1d
    cbvral
    @56
    cO
    cc
    wcel
    #
    vz
    cU
    wral
    #
    @66
    @6
    wb
    #
    vz
    cU
    wral
    @67
    @7
    wb
    @56
    cU
    cc
    @2
    wf
    #
    @70
    @3
    @72
    wph
    cU
    @0
    @2
    ulmcl
    adantl
    vz
    cU
    cc
    cO
    @2
    @2
    eqid
    #
    fmpt
    sylibr
    @69
    @71
    vz
    cU
    @26
    @69
    wa
    #
    @65
    @4
    @5
    cle
    @74
    @64
    cO
    cabs
    vz
    cU
    cO
    cc
    @2
    @73
    fvmpt2
    fveq2d
    breq1d
    ralimiaa
    @66
    @6
    vz
    cU
    ralbi
    3syl
    syl5bb
    rexbidv
    mpbid
    ex
    jca
end
