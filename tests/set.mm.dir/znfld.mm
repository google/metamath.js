include "cprime.mm"
include "wcel.mm"
include "cidom.mm"
include "cfield.mm"
include "ccrg.mm"
include "cdomn.mm"
include "cn0.mm"
include "cn.mm"
include "prmnn.mm"
include "nnnn0.mm"
include "syl.mm"
include "zncrng.mm"
include "cnzr.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "c0g.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "cbs.mm"
include "wral.mm"
include "crg.mm"
include "c2o.mm"
include "cdom.mm"
include "wbr.mm"
include "crngring.mm"
include "4syl.mm"
include "chash.mm"
include "cle.mm"
include "c2.mm"
include "hash2.mm"
include "cuz.mm"
include "prmuz2.mm"
include "eluzle.mm"
include "eqid.mm"
include "znhash.mm"
include "breqtrrd.mm"
include "syl5eqbr.mm"
include "cfn.mm"
include "cvv.mm"
include "wb.mm"
include "com.mm"
include "2onn.mm"
include "nnfi.mm"
include "ax-mp.mm"
include "fvex.mm"
include "hashdom.mm"
include "mp2an.mm"
include "sylib.mm"
include "isnzr2.mm"
include "sylanbrc.mm"
include "wa.mm"
include "czrh.mm"
include "cz.mm"
include "wrex.mm"
include "wfo.mm"
include "znzrhfo.mm"
include "foelrn.mm"
include "anim12dan.mm"
include "sylan.mm"
include "reeanv.mm"
include "cmul.mm"
include "cdvds.mm"
include "euclemma.mm"
include "3expb.mm"
include "zring.mm"
include "crh.mm"
include "adantr.mm"
include "zrhrhm.mm"
include "simprl.mm"
include "simprr.mm"
include "zringbas.mm"
include "zringmulr.mm"
include "rhmmul.mm"
include "syl3anc.mm"
include "eqeq1d.mm"
include "zmulcl.mm"
include "zndvds0.mm"
include "syl2an.mm"
include "bitr3d.mm"
include "syl2anc.mm"
include "orbi12d.mm"
include "3bitr4d.mm"
include "biimpd.mm"
include "oveq12.mm"
include "eqeq1.mm"
include "orbi1d.mm"
include "orbi2d.mm"
include "sylan9bb.mm"
include "imbi12d.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "imp.mm"
include "syldan.mm"
include "ralrimivva.mm"
include "isdomn.mm"
include "isidom.mm"
include "znfi.mm"
include "fiidomfld.mm"
include "mpbid.mm"

theorem znfld
  let cN: class N
  let cY: class Y
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume zntos.y: |- Y = ( Z/nZ ` N )


  assert |- ( N e. Prime -> Y e. Field )

  proof
    cN
    cprime
    wcel
    #
    cY
    cidom
    wcel
    #
    cY
    cfield
    wcel
    #
    @0
    cY
    ccrg
    wcel
    #
    cY
    cdomn
    wcel
    #
    @1
    @0
    cN
    cn0
    wcel
    #
    @3
    @0
    cN
    cn
    wcel
    #
    @5
    cN
    prmnn
    #
    cN
    nnnn0
    #
    syl
    #
    cN
    cY
    zntos.y
    zncrng
    #
    syl
    @0
    cY
    cnzr
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cY
    cmulr
    cfv
    #
    co
    #
    cY
    c0g
    cfv
    #
    wceq
    #
    @12
    @16
    wceq
    #
    @13
    @16
    wceq
    #
    wo
    #
    wi
    #
    vy
    cY
    cbs
    cfv
    #
    wral
    vx
    @22
    wral
    @4
    @0
    cY
    crg
    wcel
    #
    c2o
    @22
    cdom
    wbr
    #
    @11
    @0
    @6
    @5
    @3
    @23
    @7
    @8
    @10
    cY
    crngring
    4syl
    #
    @0
    c2o
    chash
    cfv
    #
    @22
    chash
    cfv
    #
    cle
    wbr
    #
    @24
    @0
    @26
    c2
    @27
    cle
    hash2
    @0
    c2
    cN
    @27
    cle
    @0
    cN
    c2
    cuz
    cfv
    wcel
    c2
    cN
    cle
    wbr
    cN
    prmuz2
    c2
    cN
    eluzle
    syl
    @0
    @6
    @27
    cN
    wceq
    @7
    @22
    cN
    cY
    zntos.y
    @22
    eqid
    #
    znhash
    syl
    breqtrrd
    syl5eqbr
    c2o
    cfn
    wcel
    #
    @22
    cvv
    wcel
    @28
    @24
    wb
    c2o
    com
    wcel
    @30
    2onn
    c2o
    nnfi
    ax-mp
    cY
    cbs
    fvex
    c2o
    @22
    cvv
    hashdom
    mp2an
    sylib
    @22
    cY
    @29
    isnzr2
    sylanbrc
    @0
    @21
    vx
    vy
    @22
    @22
    @0
    @12
    @22
    wcel
    #
    @13
    @22
    wcel
    #
    wa
    #
    @12
    vz
    cv
    #
    cY
    czrh
    cfv
    #
    cfv
    #
    wceq
    #
    vz
    cz
    wrex
    #
    @13
    vw
    cv
    #
    @35
    cfv
    #
    wceq
    #
    vw
    cz
    wrex
    #
    wa
    #
    @21
    @0
    cz
    @22
    @35
    wfo
    #
    @33
    @43
    @0
    @5
    @44
    @9
    @22
    @35
    cN
    cY
    zntos.y
    @29
    @35
    eqid
    #
    znzrhfo
    syl
    @44
    @31
    @38
    @32
    @42
    vz
    cz
    @22
    @12
    @35
    foelrn
    vw
    cz
    @22
    @13
    @35
    foelrn
    anim12dan
    sylan
    @0
    @43
    @21
    @43
    @37
    @41
    wa
    #
    vw
    cz
    wrex
    vz
    cz
    wrex
    @0
    @21
    @37
    @41
    vz
    vw
    cz
    cz
    reeanv
    @0
    @46
    @21
    vz
    vw
    cz
    cz
    @0
    @34
    cz
    wcel
    #
    @39
    cz
    wcel
    #
    wa
    #
    wa
    #
    @21
    @46
    @36
    @40
    @14
    co
    #
    @16
    wceq
    #
    @36
    @16
    wceq
    #
    @40
    @16
    wceq
    #
    wo
    #
    wi
    @50
    @52
    @55
    @50
    cN
    @34
    @39
    cmul
    co
    #
    cdvds
    wbr
    #
    cN
    @34
    cdvds
    wbr
    #
    cN
    @39
    cdvds
    wbr
    #
    wo
    #
    @52
    @55
    @0
    @47
    @48
    @57
    @60
    wb
    cN
    @34
    @39
    euclemma
    3expb
    @50
    @56
    @35
    cfv
    #
    @16
    wceq
    #
    @52
    @57
    @50
    @61
    @51
    @16
    @50
    @35
    zring
    cY
    crh
    co
    wcel
    #
    @47
    @48
    @61
    @51
    wceq
    @50
    @23
    @63
    @0
    @23
    @49
    @25
    adantr
    cY
    @35
    @45
    zrhrhm
    syl
    @0
    @47
    @48
    simprl
    #
    @0
    @47
    @48
    simprr
    #
    @34
    @39
    zring
    cY
    cmul
    @14
    @35
    cz
    zringbas
    zringmulr
    @14
    eqid
    #
    rhmmul
    syl3anc
    eqeq1d
    @0
    @5
    @56
    cz
    wcel
    @62
    @57
    wb
    @49
    @9
    @34
    @39
    zmulcl
    @56
    @35
    cN
    cY
    @16
    zntos.y
    @45
    @16
    eqid
    #
    zndvds0
    syl2an
    bitr3d
    @50
    @53
    @58
    @54
    @59
    @50
    @5
    @47
    @53
    @58
    wb
    @0
    @5
    @49
    @9
    adantr
    #
    @64
    @34
    @35
    cN
    cY
    @16
    zntos.y
    @45
    @67
    zndvds0
    syl2anc
    @50
    @5
    @48
    @54
    @59
    wb
    @68
    @65
    @39
    @35
    cN
    cY
    @16
    zntos.y
    @45
    @67
    zndvds0
    syl2anc
    orbi12d
    3bitr4d
    biimpd
    @46
    @17
    @52
    @20
    @55
    @46
    @15
    @51
    @16
    @12
    @36
    @13
    @40
    @14
    oveq12
    eqeq1d
    @37
    @20
    @53
    @19
    wo
    @41
    @55
    @37
    @18
    @53
    @19
    @12
    @36
    @16
    eqeq1
    orbi1d
    @41
    @19
    @54
    @53
    @13
    @40
    @16
    eqeq1
    orbi2d
    sylan9bb
    imbi12d
    syl5ibrcom
    rexlimdvva
    syl5bir
    imp
    syldan
    ralrimivva
    vx
    vy
    @22
    cY
    @14
    @16
    @29
    @66
    @67
    isdomn
    sylanbrc
    cY
    isidom
    sylanbrc
    @0
    @22
    cfn
    wcel
    #
    @1
    @2
    wb
    @0
    @6
    @69
    @7
    @22
    cN
    cY
    zntos.y
    @29
    znfi
    syl
    @22
    cY
    @29
    fiidomfld
    syl
    mpbid
end
