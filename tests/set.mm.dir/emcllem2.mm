include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cfz.mm"
include "cv.mm"
include "cdiv.mm"
include "csu.mm"
include "clog.mm"
include "cmin.mm"
include "peano2nn.mm"
include "nnrecred.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "nnrp.mm"
include "resubcld.mm"
include "fzfid.mm"
include "wa.mm"
include "elfznn.mm"
include "adantl.mm"
include "fsumrecl.mm"
include "ce.mm"
include "rpreccld.mm"
include "rpge0d.mm"
include "clt.mm"
include "1div1e1.mm"
include "cr.mm"
include "crp.mm"
include "1re.mm"
include "ltaddrp.mm"
include "sylancr.mm"
include "cc.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "nncn.mm"
include "addcom.mm"
include "breqtrd.mm"
include "syl5eqbr.mm"
include "cc0.mm"
include "wb.mm"
include "nnred.mm"
include "nngt0d.mm"
include "0lt1.mm"
include "ltrec1.mm"
include "mpanl12.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "eflegeo.mm"
include "recnd.mm"
include "nnne0.mm"
include "nnne0d.mm"
include "recdivd.mm"
include "1cnd.mm"
include "divsubdird.mm"
include "pncan.mm"
include "sylancl.mm"
include "oveq1d.mm"
include "dividd.mm"
include "3eqtr3rd.mm"
include "oveq2d.mm"
include "rpdivcld.mm"
include "reeflogd.mm"
include "3eqtr4d.mm"
include "relogdivd.mm"
include "eqeltrd.mm"
include "efle.mm"
include "mpbird.mm"
include "leadd2dd.mm"
include "cuz.mm"
include "id.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "oveq2.mm"
include "fsump1.mm"
include "addsub12d.mm"
include "3brtr4d.mm"
include "lesubadd2d.mm"
include "sumeq1d.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "logdifbnd.mm"
include "subadd23d.mm"
include "leaddsub.mm"
include "syl3anc.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "jca.mm"

theorem emcllem2
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cN: class N
  let vi: setvar i
  let vk: setvar k
  let vx: setvar x
  let cH: class H
  let cT: class T
  assume emcl.1: |- F = ( n e. NN |-> ( sum_ m e. ( 1 ... n ) ( 1 / m ) - ( log ` n ) ) )
  assume emcl.2: |- G = ( n e. NN |-> ( sum_ m e. ( 1 ... n ) ( 1 / m ) - ( log ` ( n + 1 ) ) ) )

  disjoint m n
  disjoint N m
  disjoint N n
  disjoint i k
  disjoint i x
  disjoint F i
  disjoint k x
  disjoint F k
  disjoint F x
  disjoint G i
  disjoint G k
  disjoint G x
  disjoint k m
  disjoint H k
  disjoint H m
  disjoint k n
  disjoint T k
  disjoint m x
  disjoint T m
  disjoint n x
  disjoint T n
  disjoint T x
  assert |- ( N e. NN -> ( ( F ` ( N + 1 ) ) <_ ( F ` N ) /\ ( G ` N ) <_ ( G ` ( N + 1 ) ) ) )

  proof
    cN
    cn
    wcel
    #
    cN
    c1
    caddc
    co
    #
    cF
    cfv
    #
    cN
    cF
    cfv
    #
    cle
    wbr
    cN
    cG
    cfv
    #
    @1
    cG
    cfv
    #
    cle
    wbr
    @0
    c1
    @1
    cfz
    co
    #
    c1
    vm
    cv
    #
    cdiv
    co
    #
    vm
    csu
    #
    @1
    clog
    cfv
    #
    cmin
    co
    #
    c1
    cN
    cfz
    co
    #
    @8
    vm
    csu
    #
    cN
    clog
    cfv
    #
    cmin
    co
    #
    @2
    @3
    cle
    @0
    @11
    @15
    cle
    wbr
    @9
    @10
    @15
    caddc
    co
    #
    cle
    wbr
    @0
    @13
    c1
    @1
    cdiv
    co
    #
    caddc
    co
    #
    @13
    @10
    @14
    cmin
    co
    #
    caddc
    co
    @9
    @16
    cle
    @0
    @17
    @19
    @13
    @0
    @1
    cN
    peano2nn
    #
    nnrecred
    #
    @0
    @10
    @14
    @0
    @1
    @0
    @1
    @20
    nnrpd
    #
    relogcld
    #
    @0
    cN
    cN
    nnrp
    #
    relogcld
    #
    resubcld
    #
    @0
    @12
    @8
    vm
    @0
    c1
    cN
    fzfid
    @0
    @7
    @12
    wcel
    #
    wa
    @7
    @27
    @7
    cn
    wcel
    #
    @0
    @7
    cN
    elfznn
    adantl
    nnrecred
    fsumrecl
    #
    @0
    @17
    @1
    cN
    cdiv
    co
    #
    clog
    cfv
    #
    @19
    cle
    @0
    @17
    @31
    cle
    wbr
    #
    @17
    ce
    cfv
    #
    @31
    ce
    cfv
    #
    cle
    wbr
    #
    @0
    @33
    c1
    c1
    @17
    cmin
    co
    #
    cdiv
    co
    #
    @34
    cle
    @0
    @17
    @21
    @0
    @17
    @0
    @1
    @22
    rpreccld
    rpge0d
    @0
    c1
    c1
    cdiv
    co
    #
    @1
    clt
    wbr
    #
    @17
    c1
    clt
    wbr
    #
    @0
    @38
    c1
    @1
    clt
    1div1e1
    @0
    c1
    c1
    cN
    caddc
    co
    #
    @1
    clt
    @0
    c1
    cr
    wcel
    #
    cN
    crp
    wcel
    c1
    @41
    clt
    wbr
    1re
    @24
    c1
    cN
    ltaddrp
    sylancr
    @0
    c1
    cc
    wcel
    #
    cN
    cc
    wcel
    #
    @41
    @1
    wceq
    ax-1cn
    cN
    nncn
    #
    c1
    cN
    addcom
    sylancr
    breqtrd
    syl5eqbr
    @0
    @1
    cr
    wcel
    #
    cc0
    @1
    clt
    wbr
    #
    @39
    @40
    wb
    #
    @0
    @1
    @20
    nnred
    #
    @0
    @1
    @20
    nngt0d
    @42
    cc0
    c1
    clt
    wbr
    @46
    @47
    wa
    @48
    1re
    0lt1
    c1
    @1
    ltrec1
    mpanl12
    syl2anc
    mpbid
    eflegeo
    @0
    c1
    cN
    @1
    cdiv
    co
    #
    cdiv
    co
    @30
    @37
    @34
    @0
    cN
    @1
    @45
    @0
    @1
    @49
    recnd
    #
    cN
    nnne0
    @0
    @1
    @20
    nnne0d
    #
    recdivd
    @0
    @36
    @50
    c1
    cdiv
    @0
    @1
    c1
    cmin
    co
    #
    @1
    cdiv
    co
    @1
    @1
    cdiv
    co
    #
    @17
    cmin
    co
    @50
    @36
    @0
    @1
    c1
    @1
    @51
    @0
    1cnd
    @51
    @52
    divsubdird
    @0
    @53
    cN
    @1
    cdiv
    @0
    @44
    @43
    @53
    cN
    wceq
    @45
    ax-1cn
    cN
    c1
    pncan
    sylancl
    oveq1d
    @0
    @54
    c1
    @17
    cmin
    @0
    @1
    @51
    @52
    dividd
    oveq1d
    3eqtr3rd
    oveq2d
    @0
    @30
    @0
    @1
    cN
    @22
    @24
    rpdivcld
    reeflogd
    3eqtr4d
    breqtrd
    @0
    @17
    cr
    wcel
    @31
    cr
    wcel
    @32
    @35
    wb
    @21
    @0
    @31
    @19
    cr
    @0
    @1
    cN
    @22
    @24
    relogdivd
    #
    @26
    eqeltrd
    @17
    @31
    efle
    syl2anc
    mpbird
    @55
    breqtrd
    leadd2dd
    @0
    @8
    @17
    vm
    c1
    cN
    @0
    cN
    cn
    c1
    cuz
    cfv
    @0
    id
    nnuz
    syl6eleq
    @0
    @7
    @6
    wcel
    #
    wa
    #
    @8
    @57
    @7
    @56
    @28
    @0
    @7
    @1
    elfznn
    adantl
    nnrecred
    #
    recnd
    @7
    @1
    c1
    cdiv
    oveq2
    fsump1
    #
    @0
    @10
    @13
    @14
    @0
    @10
    @23
    recnd
    #
    @0
    @13
    @29
    recnd
    #
    @0
    @14
    @25
    recnd
    addsub12d
    3brtr4d
    @0
    @9
    @10
    @15
    @0
    @6
    @8
    vm
    @0
    c1
    @1
    fzfid
    @58
    fsumrecl
    #
    @23
    @0
    @13
    @14
    @29
    @25
    resubcld
    lesubadd2d
    mpbird
    @0
    @1
    cn
    wcel
    #
    @2
    @11
    wceq
    @20
    vn
    @1
    c1
    vn
    cv
    #
    cfz
    co
    #
    @8
    vm
    csu
    #
    @64
    clog
    cfv
    #
    cmin
    co
    #
    @11
    cn
    cF
    @64
    @1
    wceq
    #
    @66
    @9
    @67
    @10
    cmin
    @69
    @65
    @6
    @8
    vm
    @64
    @1
    c1
    cfz
    oveq2
    sumeq1d
    #
    @64
    @1
    clog
    fveq2
    oveq12d
    emcl.1
    @9
    @10
    cmin
    ovex
    fvmpt
    syl
    vn
    cN
    @68
    @15
    cn
    cF
    @64
    cN
    wceq
    #
    @66
    @13
    @67
    @14
    cmin
    @71
    @65
    @12
    @8
    vm
    @64
    cN
    c1
    cfz
    oveq2
    sumeq1d
    #
    @64
    cN
    clog
    fveq2
    oveq12d
    emcl.1
    @13
    @14
    cmin
    ovex
    fvmpt
    3brtr4d
    @0
    @13
    @10
    cmin
    co
    #
    @9
    @1
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
    @4
    @5
    cle
    @0
    @73
    @75
    caddc
    co
    #
    @9
    cle
    wbr
    #
    @73
    @76
    cle
    wbr
    #
    @0
    @13
    @75
    @10
    cmin
    co
    #
    caddc
    co
    @18
    @77
    @9
    cle
    @0
    @80
    @17
    @13
    @0
    @75
    @10
    @0
    @74
    @0
    @74
    @0
    @63
    @74
    cn
    wcel
    @20
    @1
    peano2nn
    syl
    nnrpd
    relogcld
    #
    @23
    resubcld
    @21
    @29
    @0
    @1
    crp
    wcel
    @80
    @17
    cle
    wbr
    @22
    @1
    logdifbnd
    syl
    leadd2dd
    @0
    @13
    @10
    @75
    @61
    @60
    @0
    @75
    @81
    recnd
    subadd23d
    @59
    3brtr4d
    @0
    @73
    cr
    wcel
    @75
    cr
    wcel
    @9
    cr
    wcel
    @78
    @79
    wb
    @0
    @13
    @10
    @29
    @23
    resubcld
    @81
    @62
    @73
    @75
    @9
    leaddsub
    syl3anc
    mpbid
    vn
    cN
    @66
    @64
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
    @73
    cn
    cG
    @71
    @66
    @13
    @83
    @10
    cmin
    @72
    @71
    @82
    @1
    clog
    @64
    cN
    c1
    caddc
    oveq1
    fveq2d
    oveq12d
    emcl.2
    @13
    @10
    cmin
    ovex
    fvmpt
    @0
    @63
    @5
    @76
    wceq
    @20
    vn
    @1
    @84
    @76
    cn
    cG
    @69
    @66
    @9
    @83
    @75
    cmin
    @70
    @69
    @82
    @74
    clog
    @64
    @1
    c1
    caddc
    oveq1
    fveq2d
    oveq12d
    emcl.2
    @9
    @75
    cmin
    ovex
    fvmpt
    syl
    3brtr4d
    jca
end
