include "caddc.mm"
include "c1.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cn.mm"
include "cv.mm"
include "cexp.mm"
include "cdiv.mm"
include "cmpt.mm"
include "2nn.mm"
include "a1i.mm"
include "nnmulcld.mm"
include "nnzd.mm"
include "cuz.mm"
include "cfv.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "clog.mm"
include "cpi.mm"
include "cif.mm"
include "eluzle.mm"
include "adantl.mm"
include "iftrued.mm"
include "wceq.mm"
include "eluznn.mm"
include "sylan.mm"
include "breq2.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "id.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "ifbieq12d.mm"
include "ovex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "syl.mm"
include "eqid.mm"
include "3eqtr4d.mm"
include "seqfeq.mm"
include "cneg.mm"
include "ccxp.mm"
include "nnuz.mm"
include "1zzd.mm"
include "nncnd.mm"
include "2cnd.mm"
include "1cnd.mm"
include "addcld.mm"
include "mulcld.mm"
include "cre.mm"
include "clt.mm"
include "1lt2.mm"
include "cr.mm"
include "2re.mm"
include "rere.mm"
include "ax-mp.mm"
include "breqtrri.mm"
include "zetacvg.mm"
include "climdm.mm"
include "sylib.mm"
include "cc.mm"
include "simpr.mm"
include "negcld.mm"
include "cxpcld.mm"
include "eqeltrd.mm"
include "adantr.mm"
include "sqcld.mm"
include "nnne0d.mm"
include "cz.mm"
include "2z.mm"
include "expne0d.mm"
include "divrecd.mm"
include "divassd.mm"
include "cxpnegd.mm"
include "cxpexpzd.mm"
include "eqtr2d.mm"
include "3eqtr3d.mm"
include "isermulc2.mm"
include "climrel.mm"
include "releldmi.mm"
include "divcld.mm"
include "iserex.mm"
include "mpbid.mm"
include "nnred.mm"
include "1red.mm"
include "readdcld.mm"
include "remulcld.mm"
include "nnsqcld.mm"
include "nndivred.mm"
include "peano2nnd.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "relogcld.mm"
include "rpmulcld.mm"
include "pire.mm"
include "ifcld.mm"
include "recnd.mm"
include "mpbird.mm"

theorem lgamgulmlem4
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cR: class R
  let cT: class T
  let cU: class U
  let vk: setvar k
  let vm: setvar m
  let cG: class G
  let vn: setvar n
  let vr: setvar r
  let vy: setvar y
  let vt: setvar t
  let cN: class N
  let cA: class A
  let cO: class O
  assume lgamgulm.r: |- ( ph -> R e. NN )
  assume lgamgulm.u: |- U = { x e. CC | ( ( abs ` x ) <_ R /\ A. k e. NN0 ( 1 / R ) <_ ( abs ` ( x + k ) ) ) }
  assume lgamgulm.g: |- G = ( m e. NN |-> ( z e. U |-> ( ( z x. ( log ` ( ( m + 1 ) / m ) ) ) - ( log ` ( ( z / m ) + 1 ) ) ) ) )
  assume lgamgulm.t: |- T = ( m e. NN |-> if ( ( 2 x. R ) <_ m , ( R x. ( ( 2 x. ( R + 1 ) ) / ( m ^ 2 ) ) ) , ( ( R x. ( log ` ( ( m + 1 ) / m ) ) ) + ( ( log ` ( ( R + 1 ) x. m ) ) + _pi ) ) ) )

  disjoint k m
  disjoint k x
  disjoint k z
  disjoint R k
  disjoint m x
  disjoint m z
  disjoint R m
  disjoint x z
  disjoint R x
  disjoint R z
  disjoint U m
  disjoint U z
  disjoint m ph
  disjoint ph x
  disjoint ph z
  disjoint n r
  disjoint n y
  disjoint G n
  disjoint r y
  disjoint G r
  disjoint G y
  disjoint t x
  disjoint t y
  disjoint N t
  disjoint x y
  disjoint N x
  disjoint N y
  disjoint k n
  disjoint k r
  disjoint k t
  disjoint k y
  disjoint m n
  disjoint m r
  disjoint m t
  disjoint m y
  disjoint n t
  disjoint n x
  disjoint n z
  disjoint R n
  disjoint r t
  disjoint r x
  disjoint r z
  disjoint R r
  disjoint t z
  disjoint R t
  disjoint y z
  disjoint R y
  disjoint U n
  disjoint U r
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
  disjoint ph r
  disjoint ph t
  disjoint ph y
  disjoint T n
  disjoint T r
  disjoint T y
  assert |- ( ph -> seq 1 ( + , T ) e. dom ~~> )

  proof
    wph
    caddc
    cT
    c1
    cseq
    cli
    cdm
    #
    wcel
    caddc
    cT
    c2
    cR
    cmul
    co
    #
    cseq
    #
    @0
    wcel
    wph
    @2
    caddc
    vm
    cn
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
    vm
    cv
    #
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
    cmpt
    #
    @1
    cseq
    #
    @0
    wph
    caddc
    vn
    cT
    @9
    @1
    wph
    @1
    wph
    c2
    cR
    c2
    cn
    wcel
    wph
    2nn
    a1i
    lgamgulm.r
    nnmulcld
    #
    nnzd
    wph
    vn
    cv
    #
    @1
    cuz
    cfv
    wcel
    #
    wa
    #
    @1
    @12
    cle
    wbr
    #
    cR
    @4
    @12
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
    @12
    c1
    caddc
    co
    #
    @12
    cdiv
    co
    #
    clog
    cfv
    #
    cmul
    co
    #
    @3
    @12
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
    @18
    @12
    cT
    cfv
    #
    @12
    @9
    cfv
    #
    @14
    @15
    @18
    @26
    @13
    @15
    wph
    @1
    @12
    eluzle
    adantl
    iftrued
    @14
    @12
    cn
    wcel
    #
    @28
    @27
    wceq
    #
    wph
    @1
    cn
    wcel
    @13
    @30
    @11
    @12
    @1
    eluznn
    sylan
    #
    vm
    @12
    @1
    @5
    cle
    wbr
    #
    @8
    cR
    @5
    c1
    caddc
    co
    #
    @5
    cdiv
    co
    #
    clog
    cfv
    #
    cmul
    co
    #
    @3
    @5
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
    @27
    cn
    cT
    @5
    @12
    wceq
    #
    @33
    @15
    @8
    @41
    @18
    @26
    @5
    @12
    @1
    cle
    breq2
    @42
    @7
    @17
    cR
    cmul
    @42
    @6
    @16
    @4
    cdiv
    @5
    @12
    c2
    cexp
    oveq1
    oveq2d
    oveq2d
    #
    @42
    @37
    @22
    @40
    @25
    caddc
    @42
    @36
    @21
    cR
    cmul
    @42
    @35
    @20
    clog
    @42
    @34
    @19
    @5
    @12
    cdiv
    @5
    @12
    c1
    caddc
    oveq1
    @42
    id
    oveq12d
    fveq2d
    oveq2d
    @42
    @39
    @24
    cpi
    caddc
    @42
    @38
    @23
    clog
    @5
    @12
    @3
    cmul
    oveq2
    fveq2d
    oveq1d
    oveq12d
    ifbieq12d
    lgamgulm.t
    @15
    @18
    @26
    cR
    @17
    cmul
    ovex
    #
    @22
    @25
    caddc
    ovex
    ifex
    fvmpt
    #
    syl
    @14
    @30
    @29
    @18
    wceq
    #
    @32
    vm
    @12
    @8
    @18
    cn
    @9
    @43
    @9
    eqid
    @44
    fvmpt
    #
    syl
    3eqtr4d
    seqfeq
    wph
    caddc
    @9
    c1
    cseq
    #
    @0
    wcel
    #
    @10
    @0
    wcel
    wph
    @48
    cR
    @4
    cmul
    co
    #
    caddc
    vm
    cn
    @5
    c2
    cneg
    #
    ccxp
    co
    #
    cmpt
    #
    c1
    cseq
    #
    cli
    cfv
    #
    cmul
    co
    #
    cli
    wbr
    @49
    wph
    @55
    @50
    vn
    @53
    @9
    c1
    cn
    nnuz
    wph
    1zzd
    wph
    cR
    @4
    wph
    cR
    lgamgulm.r
    nncnd
    #
    wph
    c2
    @3
    wph
    2cnd
    #
    wph
    cR
    c1
    @57
    wph
    1cnd
    addcld
    mulcld
    mulcld
    wph
    @54
    @0
    wcel
    @54
    @55
    cli
    wbr
    wph
    c2
    vn
    @53
    @58
    c1
    c2
    cre
    cfv
    #
    clt
    wbr
    wph
    c1
    c2
    @59
    clt
    1lt2
    c2
    cr
    wcel
    #
    @59
    c2
    wceq
    2re
    c2
    rere
    ax-mp
    breqtrri
    a1i
    @30
    @12
    @53
    cfv
    #
    @12
    @51
    ccxp
    co
    #
    wceq
    wph
    vm
    @12
    @52
    @62
    cn
    @53
    @5
    @12
    @51
    ccxp
    oveq1
    @53
    eqid
    @12
    @51
    ccxp
    ovex
    fvmpt
    adantl
    #
    zetacvg
    @54
    climdm
    sylib
    wph
    @30
    wa
    #
    @61
    @62
    cc
    @63
    @64
    @12
    @51
    @64
    @12
    wph
    @30
    simpr
    #
    nncnd
    #
    @64
    c2
    @64
    2cnd
    #
    negcld
    cxpcld
    eqeltrd
    @64
    @18
    @50
    @62
    cmul
    co
    #
    @29
    @50
    @61
    cmul
    co
    @64
    @50
    @16
    cdiv
    co
    @50
    c1
    @16
    cdiv
    co
    #
    cmul
    co
    @18
    @68
    @64
    @50
    @16
    @64
    cR
    @4
    wph
    cR
    cc
    wcel
    @30
    @57
    adantr
    #
    @64
    c2
    @3
    @67
    @64
    cR
    c1
    @70
    @64
    1cnd
    addcld
    mulcld
    #
    mulcld
    @64
    @12
    @66
    sqcld
    #
    @64
    @12
    c2
    @66
    @64
    @12
    @65
    nnne0d
    #
    c2
    cz
    wcel
    @64
    2z
    a1i
    #
    expne0d
    #
    divrecd
    @64
    cR
    @4
    @16
    @70
    @71
    @72
    @75
    divassd
    @64
    @69
    @62
    @50
    cmul
    @64
    @62
    c1
    @12
    c2
    ccxp
    co
    #
    cdiv
    co
    @69
    @64
    @12
    c2
    @66
    @73
    @67
    cxpnegd
    @64
    @76
    @16
    c1
    cdiv
    @64
    @12
    c2
    @66
    @73
    @74
    cxpexpzd
    oveq2d
    eqtr2d
    oveq2d
    3eqtr3d
    @30
    @46
    wph
    @47
    adantl
    #
    @64
    @61
    @62
    @50
    cmul
    @63
    oveq2d
    3eqtr4d
    isermulc2
    @48
    @56
    cli
    climrel
    releldmi
    syl
    wph
    vn
    @9
    c1
    @1
    cn
    nnuz
    @11
    @64
    @29
    @18
    cc
    @77
    @64
    cR
    @17
    @70
    @64
    @4
    @16
    @71
    @72
    @75
    divcld
    mulcld
    eqeltrd
    iserex
    mpbid
    eqeltrd
    wph
    vn
    cT
    c1
    @1
    cn
    nnuz
    @11
    @64
    @28
    @64
    @28
    @27
    cr
    @30
    @31
    wph
    @45
    adantl
    @64
    @15
    @18
    @26
    cr
    @64
    cR
    @17
    @64
    cR
    wph
    cR
    cn
    wcel
    @30
    lgamgulm.r
    adantr
    #
    nnred
    #
    @64
    @4
    @16
    @64
    c2
    @3
    @60
    @64
    2re
    a1i
    @64
    cR
    c1
    @79
    @64
    1red
    readdcld
    remulcld
    @64
    @12
    @65
    nnsqcld
    nndivred
    remulcld
    @64
    @22
    @25
    @64
    cR
    @21
    @79
    @64
    @20
    @64
    @19
    @12
    @64
    @19
    @64
    @12
    @65
    peano2nnd
    nnrpd
    @64
    @12
    @65
    nnrpd
    #
    rpdivcld
    relogcld
    remulcld
    @64
    @24
    cpi
    @64
    @23
    @64
    @3
    @12
    @64
    @3
    @64
    cR
    @78
    peano2nnd
    nnrpd
    @80
    rpmulcld
    relogcld
    cpi
    cr
    wcel
    @64
    pire
    a1i
    readdcld
    readdcld
    ifcld
    eqeltrd
    recnd
    iserex
    mpbird
end
