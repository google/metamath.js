include "crp.mm"
include "c1.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cmu.mm"
include "cdiv.mm"
include "clog.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "wtru.mm"
include "cr.mm"
include "wss.mm"
include "cc.mm"
include "rpssre.mm"
include "ax-1cn.mm"
include "o1const.mm"
include "mp2an.mm"
include "wa.mm"
include "1cnd.mm"
include "fzfid.mm"
include "cn.mm"
include "cz.mm"
include "elfznn.mm"
include "adantl.mm"
include "mucl.mm"
include "syl.mm"
include "zred.mm"
include "nndivred.mm"
include "nnrpd.mm"
include "rpdivcl.mm"
include "sylan2.mm"
include "relogcld.mm"
include "remulcld.mm"
include "recnd.mm"
include "fsumcl.mm"
include "cmin.mm"
include "mulogsumlem.mm"
include "cvv.mm"
include "sumex.mm"
include "a1i.mm"
include "o1mptrcl.mm"
include "subcld.mm"
include "1red.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "ssriv.mm"
include "sselda.mm"
include "cc0.mm"
include "wne.mm"
include "rpcnne0d.mm"
include "reccl.mm"
include "simpl.mm"
include "syl2an.mm"
include "subdid.mm"
include "sumeq2dv.mm"
include "mulcld.mm"
include "adantlr.mm"
include "fsumsub.mm"
include "cdvds.mm"
include "crab.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rpre.mm"
include "adantr.mm"
include "ssrab2.mm"
include "simprr.mm"
include "sseldi.mm"
include "zcnd.mm"
include "nnrecred.mm"
include "adantrr.mm"
include "dvdsflsumcom.mm"
include "1div1e1.mm"
include "syl6eq.mm"
include "cuz.mm"
include "flge1nn.mm"
include "sylan.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "eluzfz1.mm"
include "musumsum.mm"
include "divdiv1.mm"
include "syl3anc.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divrecd.mm"
include "nnmulcl.mm"
include "3eqtr3rd.mm"
include "fsummulc2.mm"
include "eqtr4d.mm"
include "oveq1d.mm"
include "3eqtrd.mm"
include "o1eq.mm"
include "mpbii.mm"
include "o1dif.mm"
include "trud.mm"

theorem mulogsum
  let vx: setvar x
  let vn: setvar n
  let vk: setvar k
  let vm: setvar m
  let vy: setvar y

  disjoint n x
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint n y
  disjoint x y
  assert |- ( x e. RR+ |-> sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( ( mmu ` n ) / n ) x. ( log ` ( x / n ) ) ) ) e. O(1)

  proof
    vx
    crp
    c1
    vx
    cv
    #
    cfl
    cfv
    #
    cfz
    co
    #
    vn
    cv
    #
    cmu
    cfv
    #
    @3
    cdiv
    co
    #
    @0
    @3
    cdiv
    co
    #
    clog
    cfv
    #
    cmul
    co
    #
    vn
    csu
    #
    cmpt
    co1
    wcel
    #
    wtru
    vx
    crp
    c1
    cmpt
    co1
    wcel
    #
    @10
    crp
    cr
    wss
    c1
    cc
    wcel
    @11
    rpssre
    ax-1cn
    vx
    crp
    c1
    o1const
    mp2an
    wtru
    vx
    crp
    c1
    @9
    wtru
    @0
    crp
    wcel
    #
    wa
    #
    1cnd
    #
    @12
    @9
    cc
    wcel
    wtru
    @12
    @2
    @8
    vn
    @12
    c1
    @1
    fzfid
    @12
    @3
    @2
    wcel
    #
    wa
    #
    @8
    @16
    @5
    @7
    @16
    @4
    @3
    @16
    @4
    @16
    @3
    cn
    wcel
    #
    @4
    cz
    wcel
    #
    @15
    @17
    @12
    @3
    @1
    elfznn
    #
    adantl
    #
    @3
    mucl
    #
    syl
    zred
    @20
    nndivred
    @16
    @6
    @15
    @12
    @3
    crp
    wcel
    #
    @6
    crp
    wcel
    #
    @15
    @3
    @19
    nnrpd
    #
    @0
    @3
    rpdivcl
    #
    sylan2
    relogcld
    remulcld
    recnd
    #
    fsumcl
    adantl
    #
    wtru
    vx
    crp
    @2
    @5
    c1
    @6
    cfl
    cfv
    #
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
    @7
    cmin
    co
    cmul
    co
    #
    vn
    csu
    #
    cmpt
    co1
    wcel
    #
    vx
    crp
    c1
    @9
    cmin
    co
    #
    cmpt
    co1
    wcel
    vx
    vm
    vn
    mulogsumlem
    #
    wtru
    vx
    crp
    @34
    @36
    c1
    wtru
    vx
    crp
    @34
    cvv
    @34
    cvv
    wcel
    @13
    @2
    @33
    vn
    sumex
    a1i
    @35
    wtru
    @37
    a1i
    o1mptrcl
    @13
    c1
    @9
    @14
    @27
    subcld
    wtru
    1red
    @12
    c1
    @0
    cle
    wbr
    #
    wa
    #
    @34
    @36
    wceq
    wtru
    @39
    @34
    @2
    @5
    @32
    cmul
    co
    #
    @8
    cmin
    co
    #
    vn
    csu
    @2
    @40
    vn
    csu
    #
    @9
    cmin
    co
    @36
    @39
    @2
    @33
    @41
    vn
    @39
    @15
    wa
    #
    @5
    @32
    @7
    @43
    @5
    @43
    @4
    @3
    @43
    @4
    @43
    @17
    @18
    @39
    @2
    cn
    @3
    @2
    cn
    wss
    @39
    vk
    @2
    cn
    vk
    cv
    #
    @1
    elfznn
    #
    ssriv
    a1i
    #
    sselda
    #
    @21
    syl
    #
    zred
    @47
    nndivred
    recnd
    #
    @43
    @29
    @31
    vm
    @43
    c1
    @28
    fzfid
    #
    @43
    @30
    @29
    wcel
    #
    wa
    #
    @30
    cc
    wcel
    @30
    cc0
    wne
    wa
    #
    @31
    cc
    wcel
    @52
    @30
    @52
    @30
    @51
    @30
    cn
    wcel
    #
    @43
    @30
    @28
    elfznn
    #
    adantl
    #
    nnrpd
    rpcnne0d
    #
    @30
    reccl
    syl
    #
    fsumcl
    #
    @43
    @7
    @43
    @6
    @39
    @12
    @22
    @23
    @15
    @12
    @38
    simpl
    @24
    @25
    syl2an
    relogcld
    recnd
    subdid
    sumeq2dv
    @39
    @2
    @40
    @8
    vn
    @39
    c1
    @1
    fzfid
    #
    @43
    @5
    @32
    @49
    @59
    mulcld
    @12
    @15
    @8
    cc
    wcel
    @38
    @26
    adantlr
    fsumsub
    @39
    @42
    c1
    @9
    cmin
    @39
    @2
    vy
    cv
    @44
    cdvds
    wbr
    #
    vy
    cn
    crab
    #
    @4
    c1
    @44
    cdiv
    co
    #
    cmul
    co
    #
    vn
    csu
    vk
    csu
    @2
    @29
    @4
    c1
    @3
    @30
    cmul
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    vm
    csu
    #
    vn
    csu
    c1
    @42
    @39
    vy
    @0
    @64
    @67
    vm
    vk
    vn
    @44
    @65
    wceq
    @63
    @66
    @4
    cmul
    @44
    @65
    c1
    cdiv
    oveq2
    oveq2d
    @12
    @0
    cr
    wcel
    #
    @38
    @0
    rpre
    #
    adantr
    @39
    @44
    @2
    wcel
    #
    @3
    @62
    wcel
    #
    wa
    wa
    #
    @4
    @63
    @73
    @4
    @73
    @17
    @18
    @73
    @62
    cn
    @3
    @61
    vy
    cn
    ssrab2
    @39
    @71
    @72
    simprr
    sseldi
    @21
    syl
    zcnd
    @39
    @71
    @63
    cc
    wcel
    @72
    @39
    @71
    wa
    #
    @63
    @74
    @44
    @71
    @44
    cn
    wcel
    @39
    @45
    adantl
    nnrecred
    recnd
    #
    adantrr
    mulcld
    dvdsflsumcom
    @39
    @2
    @63
    c1
    vn
    vk
    vy
    @44
    c1
    wceq
    @63
    c1
    c1
    cdiv
    co
    c1
    @44
    c1
    c1
    cdiv
    oveq2
    1div1e1
    syl6eq
    @60
    @46
    @39
    @1
    c1
    cuz
    cfv
    #
    wcel
    c1
    @2
    wcel
    @39
    @1
    cn
    @76
    @12
    @69
    @38
    @1
    cn
    wcel
    @70
    @0
    flge1nn
    sylan
    nnuz
    syl6eleq
    c1
    @1
    eluzfz1
    syl
    @75
    musumsum
    @39
    @2
    @68
    @40
    vn
    @43
    @68
    @29
    @5
    @31
    cmul
    co
    #
    vm
    csu
    @40
    @43
    @29
    @67
    @77
    vm
    @52
    @5
    @30
    cdiv
    co
    #
    @4
    @65
    cdiv
    co
    #
    @77
    @67
    @52
    @4
    cc
    wcel
    #
    @3
    cc
    wcel
    @3
    cc0
    wne
    wa
    @53
    @78
    @79
    wceq
    @43
    @80
    @51
    @43
    @4
    @48
    zcnd
    adantr
    #
    @52
    @3
    @52
    @3
    @43
    @17
    @51
    @47
    adantr
    nnrpd
    rpcnne0d
    @57
    @4
    @3
    @30
    divdiv1
    syl3anc
    @52
    @5
    @30
    @43
    @5
    cc
    wcel
    @51
    @49
    adantr
    @52
    @30
    @56
    nncnd
    @52
    @30
    @56
    nnne0d
    divrecd
    @52
    @4
    @65
    @81
    @52
    @65
    @43
    @17
    @54
    @65
    cn
    wcel
    @51
    @47
    @55
    @3
    @30
    nnmulcl
    syl2an
    #
    nncnd
    @52
    @65
    @82
    nnne0d
    divrecd
    3eqtr3rd
    sumeq2dv
    @43
    @29
    @31
    @5
    vm
    @50
    @49
    @58
    fsummulc2
    eqtr4d
    sumeq2dv
    3eqtr3rd
    oveq1d
    3eqtrd
    adantl
    o1eq
    mpbii
    o1dif
    mpbii
    trud
end
