include "cfa.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "cv.mm"
include "csu.mm"
include "cmul.mm"
include "cz.mm"
include "wcel.mm"
include "ceu.mm"
include "cc0.mm"
include "cfz.mm"
include "cmin.mm"
include "cn0.mm"
include "cdiv.mm"
include "esum.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "sumeq2i.mm"
include "eqtr4i.mm"
include "nn0uz.mm"
include "eqid.mm"
include "peano2nnd.mm"
include "nnnn0d.mm"
include "wa.mm"
include "eqidd.mm"
include "cexp.mm"
include "cc.mm"
include "cmpt.mm"
include "nn0z.mm"
include "1exp.mm"
include "syl.mm"
include "oveq1d.mm"
include "mpteq2ia.mm"
include "eftval.mm"
include "adantl.mm"
include "ax-1cn.mm"
include "a1i.mm"
include "eftcl.mm"
include "sylan.mm"
include "eqeltrd.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "efcllem.mm"
include "isumsplit.mm"
include "syl5eq.mm"
include "nncnd.mm"
include "pncan.mm"
include "sylancl.mm"
include "sumeq1d.mm"
include "eqtrd.mm"
include "fzfid.mm"
include "elfznn0.mm"
include "sylan2.mm"
include "fsumcl.mm"
include "crp.mm"
include "cn.mm"
include "faccl.mm"
include "nnrpd.mm"
include "rpreccld.mm"
include "isumrpcl.mm"
include "rpred.mm"
include "recnd.mm"
include "pncan2d.mm"
include "ere.mm"
include "recni.mm"
include "subdid.mm"
include "eqtr3d.mm"
include "zcnd.mm"
include "nnne0d.mm"
include "div12d.mm"
include "cle.mm"
include "wbr.mm"
include "nnred.mm"
include "leidd.mm"
include "facdiv.mm"
include "syl3anc.mm"
include "nnzd.mm"
include "zmulcld.mm"
include "fsummulc2.mm"
include "adantr.mm"
include "wne.mm"
include "facne0.mm"
include "divrecd.mm"
include "eqtr4d.mm"
include "permnn.mm"
include "fsumzcl.mm"
include "zsubcld.mm"
include "clt.mm"
include "wn.mm"
include "0zd.mm"
include "rpmulcld.mm"
include "rpgt0d.mm"
include "nnmulcld.mm"
include "nndivred.mm"
include "nnrecred.mm"
include "cabs.mm"
include "abs1.mm"
include "oveq1i.mm"
include "mpteq2i.mm"
include "1le1.mm"
include "eqbrtri.mm"
include "eftlub.mm"
include "cr.mm"
include "rprege0d.mm"
include "absid.mm"
include "mulid2d.mm"
include "3brtr3d.mm"
include "readdcld.mm"
include "remulcld.mm"
include "1red.mm"
include "nnge1d.mm"
include "wb.mm"
include "1nn.mm"
include "nnleltp1.mm"
include "sylancr.mm"
include "mpbid.mm"
include "ltadd2dd.mm"
include "c2.mm"
include "2timesd.mm"
include "df-2.mm"
include "leadd1dd.mm"
include "syl5eqbr.mm"
include "2re.mm"
include "nngt0d.mm"
include "lemul1.mm"
include "syl112anc.mm"
include "eqbrtrrd.mm"
include "ltletrd.mm"
include "facp1.mm"
include "divcan3d.mm"
include "3eqtr3rd.mm"
include "mul32d.mm"
include "breqtrd.mm"
include "ltdivmul.mm"
include "mpbird.mm"
include "lelttrd.mm"
include "ltmuldiv2d.mm"
include "0p1e1.mm"
include "syl6breqr.mm"
include "btwnnz.mm"
include "pm2.65i.mm"

theorem eirrlem
  let wph: wff ph
  let cP: class P
  let cQ: class Q
  let vn: setvar n
  let cF: class F
  let vk: setvar k
  assume eirr.1: |- F = ( n e. NN0 |-> ( 1 / ( ! ` n ) ) )
  assume eirr.2: |- ( ph -> P e. ZZ )
  assume eirr.3: |- ( ph -> Q e. NN )
  assume eirr.4: |- ( ph -> _e = ( P / Q ) )

  disjoint Q n
  disjoint F k
  disjoint k ph
  disjoint k n
  disjoint Q k
  assert |- -. ph

  proof
    wph
    cQ
    cfa
    cfv
    #
    cQ
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    vk
    cv
    #
    cF
    cfv
    #
    vk
    csu
    #
    cmul
    co
    #
    cz
    wcel
    #
    wph
    @6
    @0
    ceu
    cmul
    co
    #
    @0
    cc0
    cQ
    cfz
    co
    #
    @4
    vk
    csu
    #
    cmul
    co
    #
    cmin
    co
    #
    cz
    wph
    @0
    ceu
    @10
    cmin
    co
    #
    cmul
    co
    @6
    @12
    wph
    @13
    @5
    @0
    cmul
    wph
    @13
    @10
    @5
    caddc
    co
    #
    @10
    cmin
    co
    @5
    wph
    ceu
    @14
    @10
    cmin
    wph
    ceu
    cc0
    @1
    c1
    cmin
    co
    #
    cfz
    co
    #
    @4
    vk
    csu
    #
    @5
    caddc
    co
    #
    @14
    wph
    ceu
    cn0
    @4
    vk
    csu
    #
    @18
    ceu
    cn0
    c1
    @3
    cfa
    cfv
    #
    cdiv
    co
    #
    vk
    csu
    @19
    vk
    esum
    cn0
    @4
    @21
    vk
    vn
    @3
    c1
    vn
    cv
    #
    cfa
    cfv
    #
    cdiv
    co
    #
    @21
    cn0
    cF
    @22
    @3
    wceq
    @23
    @20
    c1
    cdiv
    @22
    @3
    cfa
    fveq2
    oveq2d
    eirr.1
    c1
    @20
    cdiv
    ovex
    fvmpt
    #
    sumeq2i
    eqtr4i
    wph
    @4
    vk
    cF
    cc0
    @1
    @2
    cn0
    nn0uz
    @2
    eqid
    #
    wph
    @1
    wph
    cQ
    eirr.3
    peano2nnd
    #
    nnnn0d
    #
    wph
    @3
    cn0
    wcel
    #
    wa
    #
    @4
    eqidd
    #
    @30
    @4
    c1
    @3
    cexp
    co
    @20
    cdiv
    co
    #
    cc
    @29
    @4
    @32
    wceq
    wph
    c1
    vn
    cF
    @3
    cF
    vn
    cn0
    @24
    cmpt
    vn
    cn0
    c1
    @22
    cexp
    co
    #
    @23
    cdiv
    co
    #
    cmpt
    #
    eirr.1
    vn
    cn0
    @34
    @24
    @22
    cn0
    wcel
    #
    @33
    c1
    @23
    cdiv
    @36
    @22
    cz
    wcel
    @33
    c1
    wceq
    @22
    nn0z
    @22
    1exp
    syl
    oveq1d
    mpteq2ia
    eqtr4i
    #
    eftval
    adantl
    wph
    c1
    cc
    wcel
    #
    @29
    @32
    cc
    wcel
    @38
    wph
    ax-1cn
    a1i
    #
    c1
    @3
    eftcl
    sylan
    eqeltrd
    #
    wph
    @38
    caddc
    cF
    cc0
    cseq
    cli
    cdm
    wcel
    @39
    c1
    vn
    cF
    @37
    efcllem
    syl
    #
    isumsplit
    syl5eq
    wph
    @17
    @10
    @5
    caddc
    wph
    @16
    @9
    @4
    vk
    wph
    @15
    cQ
    cc0
    cfz
    wph
    cQ
    cc
    wcel
    @38
    @15
    cQ
    wceq
    wph
    cQ
    eirr.3
    nncnd
    #
    ax-1cn
    cQ
    c1
    pncan
    sylancl
    oveq2d
    sumeq1d
    oveq1d
    eqtrd
    oveq1d
    wph
    @10
    @5
    wph
    @9
    @4
    vk
    wph
    cc0
    cQ
    fzfid
    #
    @3
    @9
    wcel
    #
    wph
    @29
    @4
    cc
    wcel
    @3
    cQ
    elfznn0
    #
    @40
    sylan2
    #
    fsumcl
    #
    wph
    @5
    wph
    @5
    wph
    @4
    vk
    cF
    cc0
    @1
    @2
    cn0
    nn0uz
    @26
    @28
    @31
    @30
    @4
    @21
    crp
    @29
    @4
    @21
    wceq
    #
    wph
    @25
    adantl
    @30
    @20
    @30
    @20
    @29
    @20
    cn
    wcel
    #
    wph
    @3
    faccl
    adantl
    #
    nnrpd
    rpreccld
    eqeltrd
    @41
    isumrpcl
    #
    rpred
    #
    recnd
    pncan2d
    eqtrd
    oveq2d
    wph
    @0
    ceu
    @10
    wph
    @0
    wph
    cQ
    cn0
    wcel
    #
    @0
    cn
    wcel
    wph
    cQ
    eirr.3
    nnnn0d
    #
    cQ
    faccl
    syl
    #
    nncnd
    #
    ceu
    cc
    wcel
    wph
    ceu
    ere
    recni
    a1i
    @47
    subdid
    eqtr3d
    wph
    @8
    @11
    wph
    @8
    cP
    @0
    cQ
    cdiv
    co
    #
    cmul
    co
    #
    cz
    wph
    @8
    @0
    cP
    cQ
    cdiv
    co
    #
    cmul
    co
    @58
    wph
    ceu
    @59
    @0
    cmul
    eirr.4
    oveq2d
    wph
    @0
    cP
    cQ
    @56
    wph
    cP
    eirr.2
    zcnd
    @42
    wph
    cQ
    eirr.3
    nnne0d
    div12d
    eqtrd
    wph
    cP
    @57
    eirr.2
    wph
    @57
    wph
    @53
    cQ
    cn
    wcel
    #
    cQ
    cQ
    cle
    wbr
    @57
    cn
    wcel
    @54
    eirr.3
    wph
    cQ
    wph
    cQ
    eirr.3
    nnred
    #
    leidd
    cQ
    cQ
    facdiv
    syl3anc
    nnzd
    zmulcld
    eqeltrd
    wph
    @11
    @9
    @0
    @4
    cmul
    co
    #
    vk
    csu
    cz
    wph
    @9
    @4
    @0
    vk
    @43
    @56
    @46
    fsummulc2
    wph
    @9
    @62
    vk
    @43
    wph
    @44
    wa
    #
    @62
    @63
    @62
    @0
    @20
    cdiv
    co
    #
    cn
    @63
    @62
    @0
    @21
    cmul
    co
    @64
    @63
    @4
    @21
    @0
    cmul
    @63
    @29
    @48
    @44
    @29
    wph
    @45
    adantl
    #
    @25
    syl
    oveq2d
    @63
    @0
    @20
    wph
    @0
    cc
    wcel
    @44
    @56
    adantr
    @63
    @20
    @44
    wph
    @29
    @49
    @45
    @50
    sylan2
    nncnd
    @63
    @29
    @20
    cc0
    wne
    @65
    @3
    facne0
    syl
    divrecd
    eqtr4d
    @44
    @64
    cn
    wcel
    wph
    @3
    cQ
    permnn
    adantl
    eqeltrd
    nnzd
    fsumzcl
    eqeltrd
    zsubcld
    eqeltrd
    wph
    cc0
    cz
    wcel
    cc0
    @6
    clt
    wbr
    @6
    cc0
    c1
    caddc
    co
    #
    clt
    wbr
    @7
    wn
    wph
    0zd
    wph
    @6
    wph
    @0
    @5
    wph
    @0
    @55
    nnrpd
    #
    @51
    rpmulcld
    rpgt0d
    wph
    @6
    c1
    @66
    clt
    wph
    @6
    c1
    clt
    wbr
    @5
    c1
    @0
    cdiv
    co
    #
    clt
    wbr
    wph
    @5
    @1
    c1
    caddc
    co
    #
    @1
    cfa
    cfv
    #
    @1
    cmul
    co
    #
    cdiv
    co
    #
    @68
    @52
    wph
    @69
    @71
    wph
    @69
    wph
    @1
    @27
    peano2nnd
    nnred
    #
    wph
    @70
    @1
    wph
    @1
    cn0
    wcel
    @70
    cn
    wcel
    @28
    @1
    faccl
    syl
    #
    @27
    nnmulcld
    #
    nndivred
    #
    wph
    @0
    @55
    nnrecred
    #
    wph
    @5
    cabs
    cfv
    #
    c1
    cabs
    cfv
    #
    @1
    cexp
    co
    #
    @72
    cmul
    co
    #
    @5
    @72
    cle
    wph
    c1
    vk
    vn
    cF
    cF
    vn
    cn0
    @80
    @70
    cdiv
    co
    c1
    @69
    cdiv
    co
    @22
    cexp
    co
    cmul
    co
    cmpt
    #
    @1
    @37
    cF
    @35
    vn
    cn0
    @79
    @22
    cexp
    co
    #
    @23
    cdiv
    co
    #
    cmpt
    @37
    vn
    cn0
    @84
    @34
    @83
    @33
    @23
    cdiv
    @79
    c1
    @22
    cexp
    abs1
    oveq1i
    oveq1i
    mpteq2i
    eqtr4i
    @82
    eqid
    @27
    @39
    @79
    c1
    cle
    wbr
    wph
    @79
    c1
    c1
    cle
    abs1
    1le1
    eqbrtri
    a1i
    eftlub
    wph
    @5
    cr
    wcel
    cc0
    @5
    cle
    wbr
    wa
    @78
    @5
    wceq
    wph
    @5
    @51
    rprege0d
    @5
    absid
    syl
    wph
    @81
    c1
    @72
    cmul
    co
    @72
    wph
    @80
    c1
    @72
    cmul
    wph
    @80
    c1
    @1
    cexp
    co
    #
    c1
    @79
    c1
    @1
    cexp
    abs1
    oveq1i
    wph
    @1
    cz
    wcel
    @85
    c1
    wceq
    wph
    @1
    @27
    nnzd
    @1
    1exp
    syl
    syl5eq
    oveq1d
    wph
    @72
    wph
    @72
    @76
    recnd
    mulid2d
    eqtrd
    3brtr3d
    wph
    @72
    @68
    clt
    wbr
    #
    @69
    @71
    @68
    cmul
    co
    #
    clt
    wbr
    #
    wph
    @69
    @1
    @1
    cmul
    co
    #
    @87
    clt
    wph
    @69
    @1
    @1
    caddc
    co
    #
    @89
    @73
    wph
    @1
    @1
    wph
    @1
    @27
    nnred
    #
    @91
    readdcld
    wph
    @1
    @1
    @91
    @91
    remulcld
    wph
    c1
    @1
    @1
    wph
    1red
    #
    @91
    @91
    wph
    c1
    cQ
    cle
    wbr
    #
    c1
    @1
    clt
    wbr
    #
    wph
    cQ
    eirr.3
    nnge1d
    #
    wph
    c1
    cn
    wcel
    @60
    @93
    @94
    wb
    1nn
    eirr.3
    c1
    cQ
    nnleltp1
    sylancr
    mpbid
    ltadd2dd
    wph
    c2
    @1
    cmul
    co
    #
    @90
    @89
    cle
    wph
    @1
    wph
    @1
    @27
    nncnd
    #
    2timesd
    wph
    c2
    @1
    cle
    wbr
    #
    @96
    @89
    cle
    wbr
    #
    wph
    c2
    c1
    c1
    caddc
    co
    @1
    cle
    df-2
    wph
    c1
    cQ
    c1
    @92
    @61
    @92
    @95
    leadd1dd
    syl5eqbr
    wph
    c2
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    @101
    cc0
    @1
    clt
    wbr
    @98
    @99
    wb
    @100
    wph
    2re
    a1i
    @91
    @91
    wph
    @1
    @27
    nngt0d
    c2
    @1
    @1
    lemul1
    syl112anc
    mpbid
    eqbrtrrd
    ltletrd
    wph
    @89
    @70
    @68
    cmul
    co
    #
    @1
    cmul
    co
    @87
    wph
    @1
    @102
    @1
    cmul
    wph
    @70
    @0
    cdiv
    co
    @0
    @1
    cmul
    co
    #
    @0
    cdiv
    co
    @102
    @1
    wph
    @70
    @103
    @0
    cdiv
    wph
    @53
    @70
    @103
    wceq
    @54
    cQ
    facp1
    syl
    oveq1d
    wph
    @70
    @0
    wph
    @70
    @74
    nncnd
    #
    @56
    wph
    @0
    @55
    nnne0d
    #
    divrecd
    wph
    @1
    @0
    @97
    @56
    @105
    divcan3d
    3eqtr3rd
    oveq1d
    wph
    @70
    @68
    @1
    @104
    wph
    @68
    @77
    recnd
    @97
    mul32d
    eqtrd
    breqtrd
    wph
    @69
    cr
    wcel
    @68
    cr
    wcel
    @71
    cr
    wcel
    cc0
    @71
    clt
    wbr
    @86
    @88
    wb
    @73
    @77
    wph
    @71
    @75
    nnred
    wph
    @71
    @75
    nngt0d
    @69
    @68
    @71
    ltdivmul
    syl112anc
    mpbird
    lelttrd
    wph
    @5
    c1
    @0
    @52
    @92
    @67
    ltmuldiv2d
    mpbird
    0p1e1
    syl6breqr
    cc0
    @6
    btwnnz
    syl3anc
    pm2.65i
end
