include "crp.mm"
include "wcel.mm"
include "clog.mm"
include "cfv.mm"
include "c2.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "cfl.mm"
include "cfa.mm"
include "cle.mm"
include "caddc.mm"
include "rpcn.mm"
include "times2d.mm"
include "oveq2d.mm"
include "relogcl.mm"
include "recnd.mm"
include "2cnd.mm"
include "subdid.mm"
include "rpre.mm"
include "remulcld.mm"
include "subsub4d.mm"
include "3eqtr4d.mm"
include "wbr.mm"
include "c1.mm"
include "cfz.mm"
include "cv.mm"
include "cdiv.mm"
include "csu.mm"
include "resubcld.mm"
include "fzfid.mm"
include "wa.mm"
include "cn.mm"
include "elfznn.mm"
include "adantl.mm"
include "nnrecred.mm"
include "fsumrecl.mm"
include "cn0.mm"
include "cr.mm"
include "cc0.mm"
include "rprege0.mm"
include "flge0nn0.mm"
include "syl.mm"
include "faccl.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "readdcld.mm"
include "reflcl.mm"
include "harmoniclbnd.mm"
include "clt.mm"
include "wb.mm"
include "rpregt0.mm"
include "lemul2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "flle.mm"
include "le2subd.mm"
include "remulcl.mm"
include "syl2an.mm"
include "peano2rem.mm"
include "adantr.mm"
include "peano2re.mm"
include "nnred.mm"
include "fllep1.mm"
include "lesub1dd.mm"
include "rpreccld.mm"
include "lemul1d.mm"
include "cc.mm"
include "nncnd.mm"
include "subdird.mm"
include "nnne0d.mm"
include "recidd.mm"
include "eqtr2d.mm"
include "chash.mm"
include "cfn.mm"
include "wceq.mm"
include "fsumconst.mm"
include "syl2anc.mm"
include "cuz.mm"
include "elfzuz3.mm"
include "hashfz.mm"
include "1cnd.mm"
include "addsubd.mm"
include "eqtr4d.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "3brtr4d.mm"
include "fsumle.mm"
include "fsummulc2.mm"
include "ax-1cn.mm"
include "sylancl.mm"
include "hashfz1.mm"
include "mulid1d.mm"
include "3eqtrrd.mm"
include "oveq12d.mm"
include "fsumsub.mm"
include "eqid.mm"
include "uztrn2.mm"
include "biantrurd.mm"
include "wss.mm"
include "uzss.mm"
include "ad2antll.mm"
include "sseld.mm"
include "pm4.71rd.mm"
include "bitr3d.mm"
include "pm5.32da.mm"
include "ancom.mm"
include "an4.mm"
include "3bitr4g.mm"
include "elfzuzb.mm"
include "anbi12i.mm"
include "anasss.mm"
include "fsumcom2.mm"
include "letrd.mm"
include "cz.mm"
include "nnz.mm"
include "flid.mm"
include "sumeq1d.mm"
include "nnre.mm"
include "nnge1.mm"
include "harmonicubnd.mm"
include "eqbrtrrd.mm"
include "fsumadd.mm"
include "logfac.mm"
include "breqtrd.mm"
include "leadd2dd.mm"
include "lesubaddd.mm"
include "mpbird.mm"
include "eqbrtrd.mm"

theorem logfaclbnd
  let cA: class A
  let vd: setvar d
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vx: setvar x


  assert |- ( A e. RR+ -> ( A x. ( ( log ` A ) - 2 ) ) <_ ( log ` ( ! ` ( |_ ` A ) ) ) )

  proof
    cA
    crp
    wcel
    #
    cA
    cA
    clog
    cfv
    #
    c2
    cmin
    co
    cmul
    co
    #
    cA
    @1
    cmul
    co
    #
    cA
    cmin
    co
    #
    cA
    cmin
    co
    #
    cA
    cfl
    cfv
    #
    cfa
    cfv
    #
    clog
    cfv
    #
    cle
    @0
    @3
    cA
    c2
    cmul
    co
    #
    cmin
    co
    @3
    cA
    cA
    caddc
    co
    #
    cmin
    co
    @2
    @5
    @0
    @9
    @10
    @3
    cmin
    @0
    cA
    cA
    rpcn
    #
    times2d
    oveq2d
    @0
    cA
    @1
    c2
    @11
    @0
    @1
    cA
    relogcl
    #
    recnd
    @0
    2cnd
    subdid
    @0
    @3
    cA
    cA
    @0
    @3
    @0
    cA
    @1
    cA
    rpre
    #
    @12
    remulcld
    #
    recnd
    @11
    @11
    subsub4d
    3eqtr4d
    @0
    @5
    @8
    cle
    wbr
    @4
    @8
    cA
    caddc
    co
    #
    cle
    wbr
    @0
    @4
    c1
    @6
    cfz
    co
    #
    c1
    vn
    cv
    #
    cfz
    co
    #
    c1
    vd
    cv
    #
    cdiv
    co
    #
    vd
    csu
    #
    vn
    csu
    #
    @15
    @0
    @3
    cA
    @14
    @13
    resubcld
    #
    @0
    @16
    @21
    vn
    @0
    c1
    @6
    fzfid
    #
    @0
    @17
    @16
    wcel
    #
    wa
    #
    @18
    @20
    vd
    @26
    c1
    @17
    fzfid
    #
    @26
    @19
    @18
    wcel
    #
    wa
    #
    @19
    @28
    @19
    cn
    wcel
    #
    @26
    @19
    @17
    elfznn
    adantl
    nnrecred
    #
    fsumrecl
    #
    fsumrecl
    #
    @0
    @8
    cA
    @0
    @7
    @0
    @7
    @0
    @6
    cn0
    wcel
    #
    @7
    cn
    wcel
    @0
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    wa
    @34
    cA
    rprege0
    cA
    flge0nn0
    syl
    #
    @6
    faccl
    syl
    nnrpd
    relogcld
    #
    @13
    readdcld
    #
    @0
    @4
    cA
    @16
    @20
    vd
    csu
    #
    cmul
    co
    #
    @6
    cmin
    co
    #
    @22
    @23
    @0
    @40
    @6
    @0
    cA
    @39
    @13
    @0
    @16
    @20
    vd
    @24
    @0
    @19
    @16
    wcel
    #
    wa
    #
    @19
    @42
    @30
    @0
    @19
    @6
    elfznn
    #
    adantl
    #
    nnrecred
    #
    fsumrecl
    #
    remulcld
    #
    @0
    @35
    @6
    cr
    wcel
    #
    @13
    cA
    reflcl
    #
    syl
    #
    resubcld
    @33
    @0
    @3
    @6
    @40
    cA
    @14
    @51
    @48
    @13
    @0
    @1
    @39
    cle
    wbr
    #
    @3
    @40
    cle
    wbr
    #
    cA
    vd
    harmoniclbnd
    @0
    @1
    cr
    wcel
    @39
    cr
    wcel
    @35
    cc0
    cA
    clt
    wbr
    wa
    @52
    @53
    wb
    @12
    @47
    cA
    rpregt0
    @1
    @39
    cA
    lemul2
    syl3anc
    mpbid
    @0
    @35
    @6
    cA
    cle
    wbr
    @13
    cA
    flle
    syl
    #
    le2subd
    @0
    @16
    cA
    @20
    cmul
    co
    #
    c1
    cmin
    co
    #
    vd
    csu
    #
    @16
    @19
    @6
    cfz
    co
    #
    @20
    vn
    csu
    #
    vd
    csu
    @41
    @22
    cle
    @0
    @16
    @56
    @59
    vd
    @24
    @43
    @55
    cr
    wcel
    #
    @56
    cr
    wcel
    @0
    @35
    @20
    cr
    wcel
    #
    @60
    @42
    @13
    @42
    @19
    @44
    nnrecred
    cA
    @20
    remulcl
    syl2an
    #
    @55
    peano2rem
    syl
    @43
    @58
    @20
    vn
    @43
    @19
    @6
    fzfid
    #
    @43
    @61
    @17
    @58
    wcel
    #
    @46
    adantr
    fsumrecl
    @43
    cA
    @19
    cmin
    co
    #
    @20
    cmul
    co
    #
    @6
    c1
    caddc
    co
    #
    @19
    cmin
    co
    #
    @20
    cmul
    co
    #
    @56
    @59
    cle
    @43
    @65
    @68
    cle
    wbr
    @66
    @69
    cle
    wbr
    @43
    cA
    @67
    @19
    @0
    @35
    @42
    @13
    adantr
    #
    @43
    @49
    @67
    cr
    wcel
    @43
    @35
    @49
    @70
    @50
    syl
    @6
    peano2re
    syl
    #
    @43
    @19
    @45
    nnred
    #
    @0
    cA
    @67
    cle
    wbr
    #
    @42
    @0
    @35
    @73
    @13
    cA
    fllep1
    syl
    adantr
    lesub1dd
    @43
    @65
    @68
    @20
    @43
    cA
    @19
    @70
    @72
    resubcld
    @43
    @67
    @19
    @71
    @72
    resubcld
    @43
    @19
    @43
    @19
    @45
    nnrpd
    rpreccld
    lemul1d
    mpbid
    @43
    @66
    @55
    @19
    @20
    cmul
    co
    #
    cmin
    co
    @56
    @43
    cA
    @19
    @20
    @0
    cA
    cc
    wcel
    @42
    @11
    adantr
    @43
    @19
    @45
    nncnd
    #
    @43
    @20
    @46
    recnd
    #
    subdird
    @43
    @74
    c1
    @55
    cmin
    @43
    @19
    @75
    @43
    @19
    @45
    nnne0d
    recidd
    oveq2d
    eqtr2d
    @43
    @59
    @58
    chash
    cfv
    #
    @20
    cmul
    co
    #
    @69
    @43
    @58
    cfn
    wcel
    @20
    cc
    wcel
    #
    @59
    @78
    wceq
    @63
    @76
    @58
    @20
    vn
    fsumconst
    syl2anc
    @43
    @77
    @68
    @20
    cmul
    @43
    @77
    @6
    @19
    cmin
    co
    c1
    caddc
    co
    #
    @68
    @43
    @6
    @19
    cuz
    cfv
    #
    wcel
    #
    @77
    @80
    wceq
    @42
    @82
    @0
    @19
    c1
    @6
    elfzuz3
    adantl
    @19
    @6
    hashfz
    syl
    @43
    @6
    c1
    @19
    @0
    @6
    cc
    wcel
    @42
    @0
    @6
    @51
    recnd
    #
    adantr
    @43
    1cnd
    #
    @75
    addsubd
    eqtr4d
    oveq1d
    eqtrd
    3brtr4d
    fsumle
    @0
    @41
    @16
    @55
    vd
    csu
    #
    @16
    c1
    vd
    csu
    #
    cmin
    co
    @57
    @0
    @40
    @85
    @6
    @86
    cmin
    @0
    @16
    @20
    cA
    vd
    @24
    @11
    @76
    fsummulc2
    @0
    @86
    @16
    chash
    cfv
    #
    c1
    cmul
    co
    #
    @6
    c1
    cmul
    co
    #
    @6
    @0
    @16
    cfn
    wcel
    #
    c1
    cc
    wcel
    #
    @86
    @88
    wceq
    @24
    ax-1cn
    @16
    c1
    vd
    fsumconst
    sylancl
    @0
    @87
    @6
    c1
    cmul
    @0
    @34
    @87
    @6
    wceq
    @36
    @6
    hashfz1
    syl
    oveq1d
    #
    @0
    @6
    @83
    mulid1d
    #
    3eqtrrd
    oveq12d
    @0
    @16
    @55
    c1
    vd
    @24
    @43
    @55
    @62
    recnd
    @84
    fsumsub
    eqtr4d
    @0
    @16
    @18
    @16
    @58
    vn
    vd
    @20
    @24
    @24
    @27
    @0
    @17
    c1
    cuz
    cfv
    #
    wcel
    #
    @6
    @17
    cuz
    cfv
    #
    wcel
    #
    wa
    #
    @19
    @94
    wcel
    #
    @17
    @81
    wcel
    #
    wa
    #
    wa
    #
    @99
    @82
    wa
    #
    @100
    @97
    wa
    #
    wa
    #
    @25
    @28
    wa
    @42
    @64
    wa
    @0
    @101
    @98
    wa
    @101
    @82
    @97
    wa
    #
    wa
    @102
    @105
    @0
    @101
    @98
    @106
    @0
    @101
    wa
    #
    @97
    @98
    @106
    @107
    @95
    @97
    @101
    @95
    @0
    c1
    @17
    @19
    @94
    @94
    eqid
    uztrn2
    adantl
    biantrurd
    @107
    @97
    @82
    @107
    @96
    @81
    @6
    @100
    @96
    @81
    wss
    @0
    @99
    @19
    @17
    uzss
    ad2antll
    sseld
    pm4.71rd
    bitr3d
    pm5.32da
    @98
    @101
    ancom
    @99
    @82
    @100
    @97
    an4
    3bitr4g
    @25
    @98
    @28
    @101
    @17
    c1
    @6
    elfzuzb
    @19
    c1
    @17
    elfzuzb
    anbi12i
    @42
    @103
    @64
    @104
    @19
    c1
    @6
    elfzuzb
    @17
    @19
    @6
    elfzuzb
    anbi12i
    3bitr4g
    @0
    @25
    @28
    @79
    @29
    @20
    @31
    recnd
    anasss
    fsumcom2
    3brtr4d
    letrd
    @0
    @22
    @8
    @6
    caddc
    co
    #
    @15
    @33
    @0
    @8
    @6
    @37
    @51
    readdcld
    @38
    @0
    @22
    @16
    @17
    clog
    cfv
    #
    c1
    caddc
    co
    #
    vn
    csu
    #
    @108
    cle
    @0
    @16
    @21
    @110
    vn
    @24
    @32
    @26
    @109
    cr
    wcel
    @110
    cr
    wcel
    @26
    @17
    @26
    @17
    @25
    @17
    cn
    wcel
    #
    @0
    @17
    @6
    elfznn
    adantl
    #
    nnrpd
    relogcld
    #
    @109
    peano2re
    syl
    @26
    @112
    @21
    @110
    cle
    wbr
    @113
    @112
    c1
    @17
    cfl
    cfv
    #
    cfz
    co
    #
    @20
    vd
    csu
    #
    @21
    @110
    cle
    @112
    @116
    @18
    @20
    vd
    @112
    @115
    @17
    c1
    cfz
    @112
    @17
    cz
    wcel
    @115
    @17
    wceq
    @17
    nnz
    @17
    flid
    syl
    oveq2d
    sumeq1d
    @112
    @17
    cr
    wcel
    c1
    @17
    cle
    wbr
    @117
    @110
    cle
    wbr
    @17
    nnre
    @17
    nnge1
    @17
    vd
    harmonicubnd
    syl2anc
    eqbrtrrd
    syl
    fsumle
    @0
    @111
    @16
    @109
    vn
    csu
    #
    @16
    c1
    vn
    csu
    #
    caddc
    co
    @108
    @0
    @16
    @109
    c1
    vn
    @24
    @26
    @109
    @114
    recnd
    @26
    1cnd
    fsumadd
    @0
    @8
    @118
    @6
    @119
    caddc
    @0
    @34
    @8
    @118
    wceq
    @36
    vn
    @6
    logfac
    syl
    @0
    @119
    @88
    @89
    @6
    @0
    @90
    @91
    @119
    @88
    wceq
    @24
    ax-1cn
    @16
    c1
    vn
    fsumconst
    sylancl
    @92
    @93
    3eqtrrd
    oveq12d
    eqtr4d
    breqtrd
    @0
    @6
    cA
    @8
    @51
    @13
    @37
    @54
    leadd2dd
    letrd
    letrd
    @0
    @4
    cA
    @8
    @23
    @13
    @37
    lesubaddd
    mpbird
    eqbrtrd
end
