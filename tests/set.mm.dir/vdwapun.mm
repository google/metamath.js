include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cvdwa.mm"
include "cfv.mm"
include "csn.mm"
include "cun.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "cmul.mm"
include "wa.mm"
include "wex.mm"
include "cfz.mm"
include "wo.mm"
include "cmin.mm"
include "wrex.mm"
include "wb.mm"
include "peano2nn0.mm"
include "vdwapval.mm"
include "syl3an1.mm"
include "cc.mm"
include "simp1.mm"
include "nn0cnd.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "eleq2d.mm"
include "cuz.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "elfzp12.mm"
include "syl.mm"
include "bitrd.mm"
include "anbi1d.mm"
include "andir.mm"
include "syl6bb.mm"
include "exbidv.mm"
include "df-rex.mm"
include "19.43.mm"
include "bicomi.mm"
include "3bitr4g.mm"
include "nncn.mm"
include "3ad2ant3.mm"
include "mul02d.mm"
include "3ad2ant2.mm"
include "addid1d.mm"
include "eqtrd.mm"
include "eqeq2d.mm"
include "c0ex.mm"
include "oveq1.mm"
include "ceqsexv.mm"
include "velsn.mm"
include "simpr.mm"
include "0p1e1.mm"
include "oveq1i.mm"
include "cz.mm"
include "1zzd.mm"
include "adantr.mm"
include "nn0zd.mm"
include "elfzelz.mm"
include "adantl.mm"
include "fzsubel.mm"
include "syl22anc.mm"
include "mpbid.mm"
include "1m1e0.mm"
include "zcnd.mm"
include "1cnd.mm"
include "subdird.mm"
include "mulid2d.mm"
include "mulcld.mm"
include "pncan3d.mm"
include "eqtr2d.mm"
include "subcl.mm"
include "addassd.mm"
include "eqtr4d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "exlimdv.mm"
include "0zd.mm"
include "peano2zm.mm"
include "fzaddel.mm"
include "npcan.mm"
include "eleqtrd.mm"
include "adddird.mm"
include "addcomd.mm"
include "ovex.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "spcev.mm"
include "anbi2d.mm"
include "rexlimdva.mm"
include "impbid.mm"
include "nnaddcl.mm"
include "3adant1.mm"
include "syld3an2.mm"
include "bitr4d.mm"
include "orbi12d.mm"
include "elun.mm"
include "syl6bbr.mm"
include "eqrdv.mm"

theorem vdwapun
  let cA: class A
  let cD: class D
  let cK: class K
  let va: setvar a
  let vd: setvar d
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vk: setvar k
  let cX: class X


  assert |- ( ( K e. NN0 /\ A e. NN /\ D e. NN ) -> ( A ( AP ` ( K + 1 ) ) D ) = ( { A } u. ( ( A + D ) ( AP ` K ) D ) ) )

  proof
    cK
    cn0
    wcel
    #
    cA
    cn
    wcel
    #
    cD
    cn
    wcel
    #
    w3a
    #
    vx
    cA
    cD
    cK
    c1
    caddc
    co
    #
    cvdwa
    cfv
    co
    #
    cA
    csn
    #
    cA
    cD
    caddc
    co
    #
    cD
    cK
    cvdwa
    cfv
    co
    #
    cun
    #
    @3
    vx
    cv
    #
    @5
    wcel
    #
    vn
    cv
    #
    cc0
    wceq
    #
    @10
    cA
    @12
    cD
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    wa
    #
    vn
    wex
    #
    @12
    cc0
    c1
    caddc
    co
    #
    cK
    cfz
    co
    #
    wcel
    #
    @16
    wa
    #
    vn
    wex
    #
    wo
    #
    @10
    @9
    wcel
    #
    @3
    @11
    @16
    vn
    cc0
    @4
    c1
    cmin
    co
    #
    cfz
    co
    #
    wrex
    #
    @24
    @0
    @4
    cn0
    wcel
    @1
    @2
    @11
    @28
    wb
    cK
    peano2nn0
    cA
    cD
    vn
    @4
    @10
    vdwapval
    syl3an1
    @3
    @12
    @27
    wcel
    #
    @16
    wa
    #
    vn
    wex
    @17
    @22
    wo
    #
    vn
    wex
    #
    @28
    @24
    @3
    @30
    @31
    vn
    @3
    @30
    @13
    @21
    wo
    #
    @16
    wa
    @31
    @3
    @29
    @33
    @16
    @3
    @29
    @12
    cc0
    cK
    cfz
    co
    #
    wcel
    #
    @33
    @3
    @27
    @34
    @12
    @3
    @26
    cK
    cc0
    cfz
    @3
    cK
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @26
    cK
    wceq
    @3
    cK
    @0
    @1
    @2
    simp1
    #
    nn0cnd
    ax-1cn
    cK
    c1
    pncan
    sylancl
    oveq2d
    eleq2d
    @3
    cK
    cc0
    cuz
    cfv
    #
    wcel
    @35
    @33
    wb
    @3
    cK
    cn0
    @39
    @38
    nn0uz
    syl6eleq
    @12
    cc0
    cK
    elfzp12
    syl
    bitrd
    anbi1d
    @13
    @21
    @16
    andir
    syl6bb
    exbidv
    @16
    vn
    @27
    df-rex
    @32
    @24
    @17
    @22
    vn
    19.43
    bicomi
    3bitr4g
    bitrd
    @3
    @24
    @10
    @6
    wcel
    #
    @10
    @8
    wcel
    #
    wo
    @25
    @3
    @18
    @40
    @23
    @41
    @3
    @10
    cA
    cc0
    cD
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @10
    cA
    wceq
    @18
    @40
    @3
    @43
    cA
    @10
    @3
    @43
    cA
    cc0
    caddc
    co
    cA
    @3
    @42
    cc0
    cA
    caddc
    @3
    cD
    @2
    @0
    cD
    cc
    wcel
    #
    @1
    cD
    nncn
    3ad2ant3
    #
    mul02d
    oveq2d
    @3
    cA
    @1
    @0
    cA
    cc
    wcel
    #
    @2
    cA
    nncn
    3ad2ant2
    #
    addid1d
    eqtrd
    eqeq2d
    @16
    @44
    vn
    cc0
    c0ex
    @13
    @15
    @43
    @10
    @13
    @14
    @42
    cA
    caddc
    @12
    cc0
    cD
    cmul
    oveq1
    oveq2d
    eqeq2d
    ceqsexv
    vx
    cA
    velsn
    3bitr4g
    @3
    @23
    @10
    @7
    vm
    cv
    #
    cD
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vm
    cc0
    cK
    c1
    cmin
    co
    #
    cfz
    co
    #
    wrex
    #
    @41
    @3
    @23
    @55
    @3
    @22
    @55
    vn
    @3
    @21
    @16
    @55
    @3
    @21
    wa
    #
    @55
    @16
    @15
    @51
    wceq
    #
    vm
    @54
    wrex
    #
    @56
    @12
    c1
    cmin
    co
    #
    @54
    wcel
    @15
    @7
    @59
    cD
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @58
    @56
    @59
    c1
    c1
    cmin
    co
    #
    @53
    cfz
    co
    #
    @54
    @56
    @12
    c1
    cK
    cfz
    co
    #
    wcel
    #
    @59
    @64
    wcel
    #
    @56
    @12
    @20
    @65
    @3
    @21
    simpr
    @19
    c1
    cK
    cfz
    0p1e1
    oveq1i
    syl6eleq
    @56
    c1
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    @12
    cz
    wcel
    #
    @68
    @66
    @67
    wb
    @56
    1zzd
    #
    @56
    cK
    @3
    @0
    @21
    @38
    adantr
    nn0zd
    @21
    @70
    @3
    @12
    @19
    cK
    elfzelz
    adantl
    #
    @71
    @12
    c1
    c1
    cK
    fzsubel
    syl22anc
    mpbid
    @63
    cc0
    @53
    cfz
    1m1e0
    oveq1i
    syl6eleq
    @56
    @15
    cA
    cD
    @60
    caddc
    co
    #
    caddc
    co
    @61
    @56
    @14
    @73
    cA
    caddc
    @56
    @73
    cD
    @14
    cD
    cmin
    co
    #
    caddc
    co
    @14
    @56
    @60
    @74
    cD
    caddc
    @56
    @60
    @14
    c1
    cD
    cmul
    co
    #
    cmin
    co
    @74
    @56
    @12
    c1
    cD
    @56
    @12
    @72
    zcnd
    #
    @56
    1cnd
    @3
    @45
    @21
    @46
    adantr
    #
    subdird
    @56
    @75
    cD
    @14
    cmin
    @56
    cD
    @77
    mulid2d
    oveq2d
    eqtrd
    oveq2d
    @56
    cD
    @14
    @77
    @56
    @12
    cD
    @76
    @77
    mulcld
    pncan3d
    eqtr2d
    oveq2d
    @56
    cA
    cD
    @60
    @3
    @47
    @21
    @48
    adantr
    @77
    @56
    @59
    cD
    @56
    @12
    cc
    wcel
    @37
    @59
    cc
    wcel
    @76
    ax-1cn
    @12
    c1
    subcl
    sylancl
    @77
    mulcld
    addassd
    eqtr4d
    @57
    @62
    vm
    @59
    @54
    @49
    @59
    wceq
    #
    @51
    @61
    @15
    @78
    @50
    @60
    @7
    caddc
    @49
    @59
    cD
    cmul
    oveq1
    oveq2d
    eqeq2d
    rspcev
    syl2anc
    @16
    @52
    @57
    vm
    @54
    @10
    @15
    @51
    eqeq1
    rexbidv
    syl5ibrcom
    expimpd
    exlimdv
    @3
    @52
    @23
    vm
    @54
    @3
    @49
    @54
    wcel
    #
    wa
    #
    @23
    @52
    @21
    @51
    @15
    wceq
    #
    wa
    #
    vn
    wex
    #
    @80
    @49
    c1
    caddc
    co
    #
    @20
    wcel
    #
    @51
    cA
    @84
    cD
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @83
    @80
    @84
    @19
    @53
    c1
    caddc
    co
    #
    cfz
    co
    #
    @20
    @80
    @79
    @84
    @90
    wcel
    #
    @3
    @79
    simpr
    @80
    cc0
    cz
    wcel
    @53
    cz
    wcel
    #
    @49
    cz
    wcel
    #
    @68
    @79
    @91
    wb
    @80
    0zd
    @80
    @69
    @92
    @80
    cK
    @3
    @0
    @79
    @38
    adantr
    #
    nn0zd
    cK
    peano2zm
    syl
    @79
    @93
    @3
    @49
    cc0
    @53
    elfzelz
    adantl
    #
    @80
    1zzd
    @49
    c1
    cc0
    @53
    fzaddel
    syl22anc
    mpbid
    @80
    @89
    cK
    @19
    cfz
    @80
    @36
    @37
    @89
    cK
    wceq
    @80
    cK
    @94
    nn0cnd
    ax-1cn
    cK
    c1
    npcan
    sylancl
    oveq2d
    eleqtrd
    @80
    @51
    cA
    cD
    @50
    caddc
    co
    #
    caddc
    co
    @87
    @80
    cA
    cD
    @50
    @3
    @47
    @79
    @48
    adantr
    @3
    @45
    @79
    @46
    adantr
    #
    @80
    @49
    cD
    @80
    @49
    @95
    zcnd
    #
    @97
    mulcld
    #
    addassd
    @80
    @86
    @96
    cA
    caddc
    @80
    @86
    @50
    @75
    caddc
    co
    #
    @96
    @80
    @49
    c1
    cD
    @98
    @80
    1cnd
    @97
    adddird
    @80
    @96
    @50
    cD
    caddc
    co
    @100
    @80
    cD
    @50
    @97
    @99
    addcomd
    @80
    @75
    cD
    @50
    caddc
    @80
    cD
    @97
    mulid2d
    oveq2d
    eqtr4d
    eqtr4d
    oveq2d
    eqtr4d
    @82
    @85
    @88
    wa
    vn
    @84
    @49
    c1
    caddc
    ovex
    @12
    @84
    wceq
    #
    @21
    @85
    @81
    @88
    @12
    @84
    @20
    eleq1
    @101
    @15
    @87
    @51
    @101
    @14
    @86
    cA
    caddc
    @12
    @84
    cD
    cmul
    oveq1
    oveq2d
    eqeq2d
    anbi12d
    spcev
    syl2anc
    @52
    @22
    @82
    vn
    @52
    @16
    @81
    @21
    @10
    @51
    @15
    eqeq1
    anbi2d
    exbidv
    syl5ibrcom
    rexlimdva
    impbid
    @0
    @7
    cn
    wcel
    #
    @1
    @2
    @41
    @55
    wb
    @1
    @2
    @102
    @0
    cA
    cD
    nnaddcl
    3adant1
    @7
    cD
    vm
    cK
    @10
    vdwapval
    syld3an2
    bitr4d
    orbi12d
    @10
    @6
    @8
    elun
    syl6bbr
    bitrd
    eqrdv
end
