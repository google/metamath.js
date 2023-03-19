include "cprime.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cexp.mm"
include "co.mm"
include "cphi.mm"
include "cfv.mm"
include "cv.mm"
include "cgcd.mm"
include "c1.mm"
include "wceq.mm"
include "cfz.mm"
include "crab.mm"
include "chash.mm"
include "cmin.mm"
include "cmul.mm"
include "cn0.mm"
include "prmnn.mm"
include "nnnn0.mm"
include "nnexpcl.mm"
include "syl2an.mm"
include "phival.mm"
include "syl.mm"
include "cc.mm"
include "nnm1nn0.mm"
include "nncnd.mm"
include "adantr.mm"
include "ax-1cn.mm"
include "subdi.mm"
include "mp3an3.mm"
include "syl2anc.mm"
include "mulid1d.mm"
include "oveq2d.mm"
include "caddc.mm"
include "cc0.mm"
include "cdvds.mm"
include "wbr.mm"
include "cun.mm"
include "cin.mm"
include "c0.mm"
include "inrab.mm"
include "wn.mm"
include "wral.mm"
include "wi.mm"
include "cz.mm"
include "wb.mm"
include "elfzelz.mm"
include "prmz.mm"
include "rpexp.mm"
include "syl3an1.mm"
include "3expa.mm"
include "an32s.mm"
include "simpr.mm"
include "zexpcl.mm"
include "gcdcom.mm"
include "eqeq1d.mm"
include "coprm.mm"
include "adantlr.mm"
include "3bitr4d.mm"
include "zcn.mm"
include "adantl.mm"
include "subid1d.mm"
include "breq2d.mm"
include "notbid.mm"
include "bitr4d.mm"
include "sylan2.mm"
include "biimpd.mm"
include "imnan.mm"
include "sylib.mm"
include "ralrimiva.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "syl5eq.mm"
include "cfn.mm"
include "wss.mm"
include "fzfi.mm"
include "ssrab2.mm"
include "ssfi.mm"
include "mp2an.mm"
include "hashun.mm"
include "mp3an12.mm"
include "wo.mm"
include "biimprd.mm"
include "con1d.mm"
include "orrd.mm"
include "rabid2.mm"
include "unrab.mm"
include "syl6reqr.mm"
include "fveq2d.mm"
include "nnnn0d.mm"
include "hashfz1.mm"
include "expm1t.mm"
include "sylan.mm"
include "3eqtrd.mm"
include "cdiv.mm"
include "cfl.mm"
include "1zzd.mm"
include "cuz.mm"
include "nn0uz.mm"
include "1m1e0.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "syl6eleq.mm"
include "0zd.mm"
include "hashdvds.mm"
include "oveq1d.mm"
include "nnne0d.mm"
include "nnz.mm"
include "expm1d.mm"
include "eqtr4d.mm"
include "nnzd.mm"
include "flid.mm"
include "eqtrd.mm"
include "oveq1i.mm"
include "0m0e0.mm"
include "eqtri.mm"
include "div0d.mm"
include "0z.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "oveq12d.mm"
include "hashcl.mm"
include "nn0cni.mm"
include "addcom.mm"
include "sylancr.mm"
include "3eqtr3rd.mm"
include "mulcld.mm"
include "a1i.mm"
include "subaddd.mm"
include "mpbird.mm"
include "3eqtrrd.mm"

theorem phiprmpw
  let cP: class P
  let cK: class K
  let vx: setvar x


  assert |- ( ( P e. Prime /\ K e. NN ) -> ( phi ` ( P ^ K ) ) = ( ( P ^ ( K - 1 ) ) x. ( P - 1 ) ) )

  proof
    cP
    cprime
    wcel
    #
    cK
    cn
    wcel
    #
    wa
    #
    cP
    cK
    cexp
    co
    #
    cphi
    cfv
    #
    vx
    cv
    #
    @3
    cgcd
    co
    #
    c1
    wceq
    #
    vx
    c1
    @3
    cfz
    co
    #
    crab
    #
    chash
    cfv
    #
    cP
    cK
    c1
    cmin
    co
    #
    cexp
    co
    #
    cP
    c1
    cmin
    co
    cmul
    co
    #
    @2
    @3
    cn
    wcel
    #
    @4
    @10
    wceq
    @0
    cP
    cn
    wcel
    #
    cK
    cn0
    wcel
    #
    @14
    @1
    cP
    prmnn
    #
    cK
    nnnn0
    #
    cP
    cK
    nnexpcl
    syl2an
    #
    vx
    @3
    phival
    syl
    @2
    @13
    @12
    cP
    cmul
    co
    #
    @12
    c1
    cmul
    co
    #
    cmin
    co
    #
    @20
    @12
    cmin
    co
    #
    @10
    @2
    @12
    cc
    wcel
    #
    cP
    cc
    wcel
    #
    @13
    @22
    wceq
    #
    @2
    @12
    @0
    @15
    @11
    cn0
    wcel
    @12
    cn
    wcel
    @1
    @17
    cK
    nnm1nn0
    cP
    @11
    nnexpcl
    syl2an
    #
    nncnd
    #
    @0
    @25
    @1
    @0
    cP
    @17
    nncnd
    #
    adantr
    #
    @24
    @25
    c1
    cc
    wcel
    @26
    ax-1cn
    @12
    cP
    c1
    subdi
    mp3an3
    syl2anc
    @2
    @21
    @12
    @20
    cmin
    @2
    @12
    @28
    mulid1d
    oveq2d
    @2
    @23
    @10
    wceq
    @12
    @10
    caddc
    co
    #
    @20
    wceq
    @2
    @9
    cP
    @5
    cc0
    cmin
    co
    #
    cdvds
    wbr
    #
    vx
    @8
    crab
    #
    cun
    #
    chash
    cfv
    #
    @10
    @34
    chash
    cfv
    #
    caddc
    co
    #
    @20
    @31
    @2
    @9
    @34
    cin
    #
    c0
    wceq
    #
    @36
    @38
    wceq
    #
    @2
    @39
    @7
    @33
    wa
    #
    vx
    @8
    crab
    #
    c0
    @7
    @33
    vx
    @8
    inrab
    @2
    @42
    wn
    #
    vx
    @8
    wral
    @43
    c0
    wceq
    @2
    @44
    vx
    @8
    @2
    @5
    @8
    wcel
    #
    wa
    #
    @7
    @33
    wn
    #
    wi
    @44
    @46
    @7
    @47
    @45
    @2
    @5
    cz
    wcel
    #
    @7
    @47
    wb
    @5
    c1
    @3
    elfzelz
    @2
    @48
    wa
    #
    @7
    cP
    @5
    cdvds
    wbr
    #
    wn
    #
    @47
    @49
    @3
    @5
    cgcd
    co
    #
    c1
    wceq
    #
    cP
    @5
    cgcd
    co
    c1
    wceq
    #
    @7
    @51
    @0
    @48
    @1
    @53
    @54
    wb
    #
    @0
    @48
    @1
    @55
    @0
    cP
    cz
    wcel
    #
    @48
    @1
    @55
    cP
    prmz
    #
    cP
    @5
    cK
    rpexp
    syl3an1
    3expa
    an32s
    @49
    @6
    @52
    c1
    @49
    @48
    @3
    cz
    wcel
    #
    @6
    @52
    wceq
    @2
    @48
    simpr
    @2
    @58
    @48
    @0
    @56
    @16
    @58
    @1
    @57
    @18
    cP
    cK
    zexpcl
    syl2an
    adantr
    @5
    @3
    gcdcom
    syl2anc
    eqeq1d
    @0
    @48
    @51
    @54
    wb
    @1
    cP
    @5
    coprm
    adantlr
    3bitr4d
    @49
    @33
    @50
    @49
    @32
    @5
    cP
    cdvds
    @49
    @5
    @48
    @5
    cc
    wcel
    @2
    @5
    zcn
    adantl
    subid1d
    breq2d
    notbid
    bitr4d
    sylan2
    #
    biimpd
    @7
    @33
    imnan
    sylib
    ralrimiva
    @42
    vx
    @8
    rabeq0
    sylibr
    syl5eq
    @9
    cfn
    wcel
    #
    @34
    cfn
    wcel
    #
    @40
    @41
    @8
    cfn
    wcel
    #
    @9
    @8
    wss
    @60
    c1
    @3
    fzfi
    #
    @7
    vx
    @8
    ssrab2
    @8
    @9
    ssfi
    mp2an
    #
    @62
    @34
    @8
    wss
    @61
    @63
    @33
    vx
    @8
    ssrab2
    @8
    @34
    ssfi
    mp2an
    @9
    @34
    hashun
    mp3an12
    syl
    @2
    @36
    @8
    chash
    cfv
    #
    @3
    @20
    @2
    @35
    @8
    chash
    @2
    @8
    @7
    @33
    wo
    #
    vx
    @8
    crab
    #
    @35
    @2
    @66
    vx
    @8
    wral
    @8
    @67
    wceq
    @2
    @66
    vx
    @8
    @46
    @7
    @33
    @46
    @33
    @7
    @46
    @7
    @47
    @59
    biimprd
    con1d
    orrd
    ralrimiva
    @66
    vx
    @8
    rabid2
    sylibr
    @7
    @33
    vx
    @8
    unrab
    syl6reqr
    fveq2d
    @2
    @3
    cn0
    wcel
    @65
    @3
    wceq
    @2
    @3
    @19
    nnnn0d
    #
    @3
    hashfz1
    syl
    @0
    @25
    @1
    @3
    @20
    wceq
    @29
    cP
    cK
    expm1t
    sylan
    3eqtrd
    @2
    @38
    @10
    @12
    caddc
    co
    #
    @31
    @2
    @37
    @12
    @10
    caddc
    @2
    @37
    @3
    cc0
    cmin
    co
    #
    cP
    cdiv
    co
    #
    cfl
    cfv
    #
    c1
    c1
    cmin
    co
    #
    cc0
    cmin
    co
    #
    cP
    cdiv
    co
    #
    cfl
    cfv
    #
    cmin
    co
    @12
    cc0
    cmin
    co
    @12
    @2
    vx
    c1
    @3
    cc0
    cP
    @0
    @15
    @1
    @17
    adantr
    #
    @2
    1zzd
    @2
    @3
    cn0
    @73
    cuz
    cfv
    #
    @68
    cn0
    cc0
    cuz
    cfv
    @78
    nn0uz
    @73
    cc0
    cuz
    1m1e0
    fveq2i
    eqtr4i
    syl6eleq
    @2
    0zd
    hashdvds
    @2
    @72
    @12
    @76
    cc0
    cmin
    @2
    @72
    @12
    cfl
    cfv
    #
    @12
    @2
    @71
    @12
    cfl
    @2
    @71
    @3
    cP
    cdiv
    co
    @12
    @2
    @70
    @3
    cP
    cdiv
    @2
    @3
    @2
    @3
    @19
    nncnd
    subid1d
    oveq1d
    @2
    cP
    cK
    @30
    @2
    cP
    @77
    nnne0d
    #
    @1
    cK
    cz
    wcel
    @0
    cK
    nnz
    adantl
    expm1d
    eqtr4d
    fveq2d
    @2
    @12
    cz
    wcel
    @79
    @12
    wceq
    @2
    @12
    @27
    nnzd
    @12
    flid
    syl
    eqtrd
    @2
    @76
    cc0
    cfl
    cfv
    #
    cc0
    @2
    @75
    cc0
    cfl
    @2
    @75
    cc0
    cP
    cdiv
    co
    cc0
    @74
    cc0
    cP
    cdiv
    @74
    cc0
    cc0
    cmin
    co
    cc0
    @73
    cc0
    cc0
    cmin
    1m1e0
    oveq1i
    0m0e0
    eqtri
    oveq1i
    @2
    cP
    @30
    @80
    div0d
    syl5eq
    fveq2d
    cc0
    cz
    wcel
    @81
    cc0
    wceq
    0z
    cc0
    flid
    ax-mp
    syl6eq
    oveq12d
    @2
    @12
    @28
    subid1d
    3eqtrd
    oveq2d
    @2
    @10
    cc
    wcel
    #
    @24
    @69
    @31
    wceq
    @10
    @60
    @10
    cn0
    wcel
    @64
    @9
    hashcl
    ax-mp
    nn0cni
    #
    @28
    @10
    @12
    addcom
    sylancr
    eqtrd
    3eqtr3rd
    @2
    @20
    @12
    @10
    @2
    @12
    cP
    @28
    @30
    mulcld
    @28
    @82
    @2
    @83
    a1i
    subaddd
    mpbird
    3eqtrrd
    eqtrd
end
