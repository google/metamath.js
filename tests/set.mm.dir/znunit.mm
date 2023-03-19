include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cfv.mm"
include "cur.mm"
include "cdsr.mm"
include "wbr.mm"
include "cv.mm"
include "cmulr.mm"
include "co.mm"
include "wceq.mm"
include "cbs.mm"
include "wrex.mm"
include "cgcd.mm"
include "c1.mm"
include "ccrg.mm"
include "wb.mm"
include "zncrng.mm"
include "adantr.mm"
include "eqid.mm"
include "crngunit.mm"
include "syl.mm"
include "wf.mm"
include "wfo.mm"
include "znzrhfo.mm"
include "fof.mm"
include "ffvelrn.mm"
include "sylancom.mm"
include "dvdsr2.mm"
include "cmul.mm"
include "cmin.mm"
include "cdvds.mm"
include "crn.mm"
include "forn.mm"
include "rexeqdv.mm"
include "wfn.mm"
include "ffn.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "rexrn.mm"
include "3syl.mm"
include "bitr3d.mm"
include "zring.mm"
include "crh.mm"
include "crg.mm"
include "crngring.mm"
include "zrhrhm.mm"
include "simpr.mm"
include "simplr.mm"
include "zringbas.mm"
include "zringmulr.mm"
include "rhmmul.mm"
include "syl3anc.mm"
include "zrh1.mm"
include "eqeq12d.mm"
include "simpll.mm"
include "zmulcld.mm"
include "1zzd.mm"
include "zndvds.mm"
include "rexbidva.mm"
include "nn0z.mm"
include "ad2antrr.mm"
include "gcddvds.mm"
include "syl2anc.mm"
include "simpld.mm"
include "wi.mm"
include "gcdcld.mm"
include "nn0zd.mm"
include "adantrr.mm"
include "dvdsmultr2.mm"
include "mpd.mm"
include "simprd.mm"
include "simprr.mm"
include "peano2zm.mm"
include "dvdstr.mm"
include "mp2and.mm"
include "dvdssub2.mm"
include "syl31anc.mm"
include "mpbid.mm"
include "dvds1.mm"
include "rexlimdvaa.mm"
include "caddc.mm"
include "bezout.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "syl5ibcom.mm"
include "cneg.mm"
include "ad3antrrr.mm"
include "dvdsmul1.mm"
include "zmulcl.mm"
include "dvdsnegb.mm"
include "zcnd.mm"
include "cc.mm"
include "zcn.mm"
include "ad2antlr.mm"
include "mulcomd.mm"
include "oveq1d.mm"
include "mulcld.mm"
include "subnegd.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "negcld.mm"
include "nncand.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "oveq2.mm"
include "breq2d.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "reximdva.mm"
include "syld.mm"
include "impbid.mm"
include "3bitrd.mm"

theorem znunit
  let cA: class A
  let cU: class U
  let cL: class L
  let cN: class N
  let cY: class Y
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let cE: class E
  assume znchr.y: |- Y = ( Z/nZ ` N )
  assume znunit.u: |- U = ( Unit ` Y )
  assume znunit.l: |- L = ( ZRHom ` Y )


  assert |- ( ( N e. NN0 /\ A e. ZZ ) -> ( ( L ` A ) e. U <-> ( A gcd N ) = 1 ) )

  proof
    cN
    cn0
    wcel
    #
    cA
    cz
    wcel
    #
    wa
    #
    cA
    cL
    cfv
    #
    cU
    wcel
    #
    @3
    cY
    cur
    cfv
    #
    cY
    cdsr
    cfv
    #
    wbr
    #
    vx
    cv
    #
    @3
    cY
    cmulr
    cfv
    #
    co
    #
    @5
    wceq
    #
    vx
    cY
    cbs
    cfv
    #
    wrex
    #
    cA
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    @2
    cY
    ccrg
    wcel
    #
    @4
    @7
    wb
    @0
    @16
    @1
    cN
    cY
    znchr.y
    zncrng
    adantr
    #
    @6
    cY
    cU
    @5
    @3
    znunit.u
    @5
    eqid
    #
    @6
    eqid
    #
    crngunit
    syl
    @2
    @3
    @12
    wcel
    #
    @7
    @13
    wb
    @0
    @1
    cz
    @12
    cL
    wf
    #
    @20
    @2
    cz
    @12
    cL
    wfo
    #
    @21
    @0
    @22
    @1
    @12
    cL
    cN
    cY
    znchr.y
    @12
    eqid
    #
    znunit.l
    znzrhfo
    adantr
    #
    cz
    @12
    cL
    fof
    syl
    #
    cz
    @12
    cA
    cL
    ffvelrn
    sylancom
    vx
    @12
    @6
    cY
    @9
    @3
    @5
    @23
    @19
    @9
    eqid
    #
    dvdsr2
    syl
    @2
    @13
    vn
    cv
    #
    cL
    cfv
    #
    @3
    @9
    co
    #
    @5
    wceq
    #
    vn
    cz
    wrex
    #
    cN
    @27
    cA
    cmul
    co
    #
    c1
    cmin
    co
    #
    cdvds
    wbr
    #
    vn
    cz
    wrex
    #
    @15
    @2
    @11
    vx
    cL
    crn
    #
    wrex
    #
    @13
    @31
    @2
    @11
    vx
    @36
    @12
    @2
    @22
    @36
    @12
    wceq
    @24
    cz
    @12
    cL
    forn
    syl
    rexeqdv
    @2
    @21
    cL
    cz
    wfn
    @37
    @31
    wb
    @25
    cz
    @12
    cL
    ffn
    @11
    @30
    vx
    vn
    cz
    cL
    @8
    @28
    wceq
    @10
    @29
    @5
    @8
    @28
    @3
    @9
    oveq1
    eqeq1d
    rexrn
    3syl
    bitr3d
    @2
    @30
    @34
    vn
    cz
    @2
    @27
    cz
    wcel
    #
    wa
    #
    @32
    cL
    cfv
    #
    c1
    cL
    cfv
    #
    wceq
    #
    @30
    @34
    @39
    @40
    @29
    @41
    @5
    @39
    cL
    zring
    cY
    crh
    co
    wcel
    #
    @38
    @1
    @40
    @29
    wceq
    @2
    @43
    @38
    @2
    cY
    crg
    wcel
    #
    @43
    @2
    @16
    @44
    @17
    cY
    crngring
    syl
    #
    cY
    cL
    znunit.l
    zrhrhm
    syl
    adantr
    @2
    @38
    simpr
    #
    @0
    @1
    @38
    simplr
    #
    @27
    cA
    zring
    cY
    cmul
    @9
    cL
    cz
    zringbas
    zringmulr
    @26
    rhmmul
    syl3anc
    @39
    @44
    @41
    @5
    wceq
    @2
    @44
    @38
    @45
    adantr
    cY
    @5
    cL
    znunit.l
    @18
    zrh1
    syl
    eqeq12d
    @39
    @0
    @32
    cz
    wcel
    #
    c1
    cz
    wcel
    #
    @42
    @34
    wb
    @0
    @1
    @38
    simpll
    @39
    @27
    cA
    @46
    @47
    zmulcld
    #
    @39
    1zzd
    @32
    c1
    cL
    cN
    cY
    znchr.y
    znunit.l
    zndvds
    syl3anc
    bitr3d
    rexbidva
    @2
    @35
    @15
    @2
    @34
    @15
    vn
    cz
    @2
    @38
    @34
    wa
    #
    wa
    #
    @14
    c1
    cdvds
    wbr
    #
    @15
    @52
    @14
    @32
    cdvds
    wbr
    #
    @53
    @52
    @14
    cA
    cdvds
    wbr
    #
    @54
    @52
    @55
    @14
    cN
    cdvds
    wbr
    #
    @52
    @1
    cN
    cz
    wcel
    #
    @55
    @56
    wa
    @0
    @1
    @51
    simplr
    #
    @0
    @57
    @1
    @51
    cN
    nn0z
    #
    ad2antrr
    #
    cA
    cN
    gcddvds
    syl2anc
    #
    simpld
    @52
    @14
    cz
    wcel
    #
    @38
    @1
    @55
    @54
    wi
    @52
    @14
    @52
    cA
    cN
    @58
    @60
    gcdcld
    #
    nn0zd
    #
    @2
    @38
    @38
    @34
    @46
    adantrr
    @58
    @14
    @27
    cA
    dvdsmultr2
    syl3anc
    mpd
    @52
    @62
    @48
    @49
    @14
    @33
    cdvds
    wbr
    #
    @54
    @53
    wb
    @64
    @2
    @38
    @48
    @34
    @50
    adantrr
    #
    @52
    1zzd
    @52
    @56
    @34
    @65
    @52
    @55
    @56
    @61
    simprd
    @2
    @38
    @34
    simprr
    @52
    @62
    @57
    @33
    cz
    wcel
    #
    @56
    @34
    wa
    @65
    wi
    @64
    @60
    @52
    @48
    @67
    @66
    @32
    peano2zm
    syl
    @14
    cN
    @33
    dvdstr
    syl3anc
    mp2and
    @14
    @32
    c1
    dvdssub2
    syl31anc
    mpbid
    @52
    @14
    cn0
    wcel
    @53
    @15
    wb
    @63
    @14
    dvds1
    syl
    mpbid
    rexlimdvaa
    @2
    @15
    c1
    cA
    @27
    cmul
    co
    #
    cN
    vm
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vm
    cz
    wrex
    #
    vn
    cz
    wrex
    #
    @35
    @2
    @14
    @71
    wceq
    #
    vm
    cz
    wrex
    vn
    cz
    wrex
    #
    @15
    @74
    @2
    @1
    @57
    @76
    @0
    @1
    simpr
    @0
    @57
    @1
    @59
    adantr
    vn
    vm
    cA
    cN
    bezout
    syl2anc
    @15
    @75
    @72
    vn
    vm
    cz
    cz
    @14
    c1
    @71
    eqeq1
    2rexbidv
    syl5ibcom
    @2
    @73
    @34
    vn
    cz
    @39
    @72
    @34
    vm
    cz
    @39
    @69
    cz
    wcel
    #
    wa
    #
    @34
    @72
    cN
    @32
    @71
    cmin
    co
    #
    cdvds
    wbr
    @78
    cN
    @70
    cneg
    #
    @79
    cdvds
    @78
    cN
    @70
    cdvds
    wbr
    #
    cN
    @80
    cdvds
    wbr
    #
    @39
    @77
    @57
    @81
    @0
    @57
    @1
    @38
    @77
    @59
    ad3antrrr
    #
    cN
    @69
    dvdsmul1
    sylancom
    @78
    @57
    @70
    cz
    wcel
    #
    @81
    @82
    wb
    @83
    @39
    @77
    @57
    @84
    @83
    cN
    @69
    zmulcl
    sylancom
    #
    cN
    @70
    dvdsnegb
    syl2anc
    mpbid
    @78
    @79
    @32
    @32
    @80
    cmin
    co
    #
    cmin
    co
    @80
    @78
    @71
    @86
    @32
    cmin
    @78
    @71
    @32
    @70
    caddc
    co
    @86
    @78
    @68
    @32
    @70
    caddc
    @78
    cA
    @27
    @78
    cA
    @39
    @1
    @77
    @47
    adantr
    zcnd
    #
    @38
    @27
    cc
    wcel
    @2
    @77
    @27
    zcn
    ad2antlr
    #
    mulcomd
    oveq1d
    @78
    @32
    @70
    @78
    @27
    cA
    @88
    @87
    mulcld
    #
    @78
    @70
    @85
    zcnd
    #
    subnegd
    eqtr4d
    oveq2d
    @78
    @32
    @80
    @89
    @78
    @70
    @90
    negcld
    nncand
    eqtrd
    breqtrrd
    @72
    @33
    @79
    cN
    cdvds
    c1
    @71
    @32
    cmin
    oveq2
    breq2d
    syl5ibrcom
    rexlimdva
    reximdva
    syld
    impbid
    3bitrd
    3bitrd
end
