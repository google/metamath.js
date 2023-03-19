include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "cvma.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "csu.mm"
include "clog.mm"
include "caddc.mm"
include "c2.mm"
include "cexp.mm"
include "cmin.mm"
include "c1.mm"
include "cfz.mm"
include "cfn.mm"
include "wss.mm"
include "fzfid.mm"
include "dvdsssfz1.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "wa.mm"
include "elrabi.mm"
include "adantl.mm"
include "syl.mm"
include "cc.mm"
include "cr.mm"
include "ad2antll.mm"
include "vmacl.mm"
include "breq1.mm"
include "elrab.mm"
include "simprbi.mm"
include "wb.mm"
include "ad2antrl.mm"
include "nndivdvds.mm"
include "mpbid.mm"
include "remulcld.mm"
include "recnd.mm"
include "anassrs.mm"
include "fsumcl.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "fsumadd.mm"
include "id.mm"
include "wceq.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "fsumdvdscom.mm"
include "ssrab2.mm"
include "simpr.mm"
include "sseldi.mm"
include "nncnd.mm"
include "adantr.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0d.mm"
include "divcan3d.mm"
include "sumeq2dv.mm"
include "dvdsdivcl.mm"
include "vmasum.mm"
include "crp.mm"
include "nnrp.mm"
include "relogdivd.mm"
include "3eqtrd.mm"
include "eqeltrd.mm"
include "fsummulc2.mm"
include "relogcl.mm"
include "subdid.mm"
include "3eqtr3d.mm"
include "mulcld.mm"
include "fsumsub.mm"
include "sqvald.mm"
include "oveq1d.mm"
include "fsummulc1.mm"
include "3eqtr2rd.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "cbvsumv.mm"
include "a1i.mm"
include "eqtrd.mm"
include "sqcld.mm"
include "npcand.mm"

theorem logsqvma
  let vx: setvar x
  let vu: setvar u
  let cN: class N
  let vd: setvar d
  let vc: setvar c
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vy: setvar y

  disjoint d u
  disjoint d x
  disjoint N d
  disjoint u x
  disjoint N u
  disjoint N x
  disjoint c d
  disjoint c i
  disjoint c j
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c u
  disjoint c x
  disjoint c y
  disjoint N c
  disjoint d i
  disjoint d j
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint d y
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i u
  disjoint i x
  disjoint i y
  disjoint N i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j u
  disjoint j x
  disjoint j y
  disjoint N j
  disjoint k m
  disjoint k n
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint N k
  disjoint m n
  disjoint m u
  disjoint m x
  disjoint m y
  disjoint N m
  disjoint n u
  disjoint n x
  disjoint n y
  disjoint N n
  disjoint u y
  disjoint x y
  disjoint N y
  assert |- ( N e. NN -> sum_ d e. { x e. NN | x || N } ( sum_ u e. { x e. NN | x || d } ( ( Lam ` u ) x. ( Lam ` ( d / u ) ) ) + ( ( Lam ` d ) x. ( log ` d ) ) ) = ( ( log ` N ) ^ 2 ) )

  proof
    cN
    cn
    wcel
    #
    vx
    cv
    #
    cN
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    @1
    vd
    cv
    #
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    vu
    cv
    #
    cvma
    cfv
    #
    @4
    @7
    cdiv
    co
    #
    cvma
    cfv
    #
    cmul
    co
    #
    vu
    csu
    #
    @4
    cvma
    cfv
    #
    @4
    clog
    cfv
    #
    cmul
    co
    #
    caddc
    co
    vd
    csu
    @3
    @12
    vd
    csu
    #
    @3
    @15
    vd
    csu
    #
    caddc
    co
    cN
    clog
    cfv
    #
    c2
    cexp
    co
    #
    @17
    cmin
    co
    #
    @17
    caddc
    co
    @19
    @0
    @3
    @12
    @15
    vd
    @0
    c1
    cN
    cfz
    co
    #
    cfn
    wcel
    @3
    @21
    wss
    @3
    cfn
    wcel
    @0
    c1
    cN
    fzfid
    cN
    vx
    dvdsssfz1
    @21
    @3
    ssfi
    syl2anc
    #
    @0
    @4
    @3
    wcel
    #
    wa
    #
    @6
    @11
    vu
    @24
    c1
    @4
    cfz
    co
    #
    cfn
    wcel
    @6
    @25
    wss
    #
    @6
    cfn
    wcel
    @24
    c1
    @4
    fzfid
    @24
    @4
    cn
    wcel
    #
    @26
    @23
    @27
    @0
    @2
    vx
    @4
    cn
    elrabi
    #
    adantl
    #
    @4
    vx
    dvdsssfz1
    syl
    @25
    @6
    ssfi
    syl2anc
    @0
    @23
    @7
    @6
    wcel
    #
    @11
    cc
    wcel
    @0
    @23
    @30
    wa
    wa
    #
    @11
    @31
    @8
    @10
    @31
    @7
    cn
    wcel
    #
    @8
    cr
    wcel
    #
    @30
    @32
    @0
    @23
    @5
    vx
    @7
    cn
    elrabi
    ad2antll
    #
    @7
    vmacl
    #
    syl
    @31
    @9
    cn
    wcel
    #
    @10
    cr
    wcel
    @31
    @7
    @4
    cdvds
    wbr
    #
    @36
    @30
    @37
    @0
    @23
    @30
    @32
    @37
    @5
    @37
    vx
    @7
    cn
    @1
    @7
    @4
    cdvds
    breq1
    elrab
    simprbi
    ad2antll
    @31
    @27
    @32
    @37
    @36
    wb
    @23
    @27
    @0
    @30
    @28
    ad2antrl
    @34
    @4
    @7
    nndivdvds
    syl2anc
    mpbid
    @9
    vmacl
    syl
    remulcld
    recnd
    #
    anassrs
    fsumcl
    @24
    @15
    @24
    @13
    @14
    @24
    @27
    @13
    cr
    wcel
    @29
    @4
    vmacl
    syl
    @24
    @4
    @24
    @4
    @29
    nnrpd
    relogcld
    remulcld
    recnd
    #
    fsumadd
    @0
    @16
    @20
    @17
    caddc
    @0
    @16
    @3
    @1
    cN
    @7
    cdiv
    co
    #
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    @8
    @7
    vk
    cv
    #
    cmul
    co
    #
    @7
    cdiv
    co
    #
    cvma
    cfv
    #
    cmul
    co
    #
    vk
    csu
    #
    vu
    csu
    @3
    @8
    @18
    cmul
    co
    #
    @8
    @7
    clog
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    vu
    csu
    #
    @20
    @0
    vx
    @11
    @47
    vd
    vu
    vk
    cN
    @0
    id
    @4
    @44
    wceq
    #
    @10
    @46
    @8
    cmul
    @54
    @9
    @45
    cvma
    @4
    @44
    @7
    cdiv
    oveq1
    fveq2d
    oveq2d
    @38
    fsumdvdscom
    @0
    @3
    @48
    @52
    vu
    @0
    @7
    @3
    wcel
    #
    wa
    #
    @8
    @42
    @46
    vk
    csu
    #
    cmul
    co
    @8
    @18
    @50
    cmin
    co
    #
    cmul
    co
    @48
    @52
    @56
    @57
    @58
    @8
    cmul
    @56
    @57
    @42
    @43
    cvma
    cfv
    #
    vk
    csu
    #
    @40
    clog
    cfv
    #
    @58
    @56
    @42
    @46
    @59
    vk
    @56
    @43
    @42
    wcel
    #
    wa
    #
    @45
    @43
    cvma
    @63
    @43
    @7
    @63
    @43
    @63
    @42
    cn
    @43
    @41
    vx
    cn
    ssrab2
    @56
    @62
    simpr
    sseldi
    #
    nncnd
    @56
    @7
    cc
    wcel
    @62
    @56
    @7
    @56
    @3
    cn
    @7
    @2
    vx
    cn
    ssrab2
    #
    @0
    @55
    simpr
    sseldi
    #
    nncnd
    adantr
    @56
    @7
    cc0
    wne
    @62
    @56
    @7
    @66
    nnne0d
    adantr
    divcan3d
    fveq2d
    #
    sumeq2dv
    @56
    @40
    cn
    wcel
    #
    @60
    @61
    wceq
    @56
    @3
    cn
    @40
    @65
    vx
    @7
    cN
    dvdsdivcl
    sseldi
    #
    vx
    @40
    vk
    vmasum
    syl
    @56
    cN
    @7
    @0
    cN
    crp
    wcel
    #
    @55
    cN
    nnrp
    #
    adantr
    #
    @56
    @7
    @66
    nnrpd
    #
    relogdivd
    3eqtrd
    oveq2d
    @56
    @42
    @46
    @8
    vk
    @56
    c1
    @40
    cfz
    co
    #
    cfn
    wcel
    @42
    @74
    wss
    #
    @42
    cfn
    wcel
    @56
    c1
    @40
    fzfid
    @56
    @68
    @75
    @69
    @40
    vx
    dvdsssfz1
    syl
    @74
    @42
    ssfi
    syl2anc
    @56
    @8
    @56
    @32
    @33
    @66
    @35
    syl
    recnd
    #
    @63
    @46
    @59
    cc
    @67
    @63
    @59
    @63
    @43
    cn
    wcel
    @59
    cr
    wcel
    @64
    @43
    vmacl
    syl
    recnd
    eqeltrd
    fsummulc2
    @56
    @8
    @18
    @50
    @76
    @56
    @70
    @18
    cc
    wcel
    #
    @72
    @70
    @18
    cN
    relogcl
    recnd
    #
    syl
    #
    @56
    @50
    @56
    @7
    @73
    relogcld
    recnd
    #
    subdid
    3eqtr3d
    sumeq2dv
    @0
    @53
    @3
    @49
    vu
    csu
    #
    @3
    @51
    vu
    csu
    #
    cmin
    co
    @20
    @0
    @3
    @49
    @51
    vu
    @22
    @56
    @8
    @18
    @76
    @79
    mulcld
    @56
    @8
    @50
    @76
    @80
    mulcld
    fsumsub
    @0
    @81
    @19
    @82
    @17
    cmin
    @0
    @19
    @18
    @18
    cmul
    co
    @3
    @8
    vu
    csu
    #
    @18
    cmul
    co
    @81
    @0
    @18
    @0
    @70
    @77
    @71
    @78
    syl
    #
    sqvald
    @0
    @83
    @18
    @18
    cmul
    vx
    cN
    vu
    vmasum
    oveq1d
    @0
    @3
    @8
    @18
    vu
    @22
    @84
    @76
    fsummulc1
    3eqtr2rd
    @82
    @17
    wceq
    @0
    @3
    @51
    @15
    vu
    vd
    @7
    @4
    wceq
    @8
    @13
    @50
    @14
    cmul
    @7
    @4
    cvma
    fveq2
    @7
    @4
    clog
    fveq2
    oveq12d
    cbvsumv
    a1i
    oveq12d
    eqtrd
    3eqtrd
    oveq1d
    @0
    @19
    @17
    @0
    @18
    @84
    sqcld
    @0
    @3
    @15
    vd
    @22
    @39
    fsumcl
    npcand
    3eqtrd
end
