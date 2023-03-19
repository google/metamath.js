include "crp.mm"
include "cv.mm"
include "clog.mm"
include "cfv.mm"
include "cfl.mm"
include "cfa.mm"
include "cdiv.mm"
include "co.mm"
include "cmin.mm"
include "cmpt.mm"
include "c1.mm"
include "crli.mm"
include "wbr.mm"
include "wtru.mm"
include "caddc.mm"
include "cc0.mm"
include "1red.mm"
include "1cnd.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "wne.mm"
include "wceq.mm"
include "cr.mm"
include "relogcl.mm"
include "adantl.mm"
include "recnd.mm"
include "rpcnne0.mm"
include "divdir.mm"
include "syl3anc.mm"
include "mpteq2dva.mm"
include "simpr.mm"
include "rerpdivcld.mm"
include "rpreccl.mm"
include "rpred.mm"
include "ccxp.mm"
include "simpld.mm"
include "cxp1d.mm"
include "oveq2d.mm"
include "1rp.mm"
include "cxploglim.mm"
include "mp1i.mm"
include "eqbrtrrd.mm"
include "ax-1cn.mm"
include "divrcnv.mm"
include "rlimadd.mm"
include "eqbrtrd.mm"
include "00id.mm"
include "syl6breq.mm"
include "peano2re.mm"
include "syl.mm"
include "cle.mm"
include "cn0.mm"
include "cn.mm"
include "rprege0.mm"
include "flge0nn0.mm"
include "faccl.mm"
include "3syl.mm"
include "nnrpd.mm"
include "subcld.mm"
include "cmul.mm"
include "cabs.mm"
include "logfacbnd3.mm"
include "clt.mm"
include "wb.mm"
include "adantrr.mm"
include "ad2antrl.mm"
include "subcl.mm"
include "sylancl.mm"
include "mulcld.mm"
include "abscld.mm"
include "rpregt0.mm"
include "lediv1.mm"
include "mpbid.mm"
include "simprd.mm"
include "divcan3d.mm"
include "oveq1d.mm"
include "divsubdir.mm"
include "sub32d.mm"
include "3eqtr4rd.mm"
include "fveq2d.mm"
include "absdivd.mm"
include "abssubd.mm"
include "absid.mm"
include "oveq12d.mm"
include "3eqtrd.mm"
include "subid1d.mm"
include "log1.mm"
include "simprr.mm"
include "logleb.mm"
include "sylancr.mm"
include "syl5eqbrr.mm"
include "ge0p1rpd.mm"
include "rpdivcld.mm"
include "eqtrd.mm"
include "3brtr4d.mm"
include "rlimsqzlem.mm"
include "trud.mm"

theorem logfacrlim
  let vx: setvar x
  let vn: setvar n
  let cA: class A
  let vk: setvar k
  let vy: setvar y
  let cN: class N


  assert |- ( x e. RR+ |-> ( ( log ` x ) - ( ( log ` ( ! ` ( |_ ` x ) ) ) / x ) ) ) ~~>r 1

  proof
    vx
    crp
    vx
    cv
    #
    clog
    cfv
    #
    @0
    cfl
    cfv
    #
    cfa
    cfv
    #
    clog
    cfv
    #
    @0
    cdiv
    co
    #
    cmin
    co
    #
    cmpt
    c1
    crli
    wbr
    wtru
    vx
    crp
    @1
    c1
    caddc
    co
    #
    @0
    cdiv
    co
    #
    @6
    cc0
    c1
    c1
    wtru
    1red
    wtru
    1cnd
    wtru
    vx
    crp
    @8
    cmpt
    #
    cc0
    cc0
    caddc
    co
    #
    cc0
    crli
    wtru
    @9
    vx
    crp
    @1
    @0
    cdiv
    co
    #
    c1
    @0
    cdiv
    co
    #
    caddc
    co
    #
    cmpt
    @10
    crli
    wtru
    vx
    crp
    @8
    @13
    wtru
    @0
    crp
    wcel
    #
    wa
    #
    @1
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @0
    cc
    wcel
    #
    @0
    cc0
    wne
    #
    wa
    #
    @8
    @13
    wceq
    @15
    @1
    @14
    @1
    cr
    wcel
    #
    wtru
    @0
    relogcl
    adantl
    #
    recnd
    #
    @15
    1cnd
    @14
    @20
    wtru
    @0
    rpcnne0
    #
    adantl
    #
    @1
    c1
    @0
    divdir
    syl3anc
    mpteq2dva
    wtru
    vx
    crp
    @11
    @12
    cc0
    cc0
    cr
    @15
    @1
    @0
    @22
    wtru
    @14
    simpr
    #
    rerpdivcld
    @15
    @12
    @14
    @12
    crp
    wcel
    wtru
    @0
    rpreccl
    adantl
    rpred
    wtru
    vx
    crp
    @1
    @0
    c1
    ccxp
    co
    #
    cdiv
    co
    #
    cmpt
    #
    vx
    crp
    @11
    cmpt
    cc0
    crli
    wtru
    vx
    crp
    @28
    @11
    @15
    @27
    @0
    @1
    cdiv
    @15
    @0
    @15
    @18
    @19
    @25
    simpld
    cxp1d
    oveq2d
    mpteq2dva
    c1
    crp
    wcel
    #
    @29
    cc0
    crli
    wbr
    wtru
    1rp
    c1
    vx
    cxploglim
    mp1i
    eqbrtrrd
    @17
    vx
    crp
    @12
    cmpt
    cc0
    crli
    wbr
    wtru
    ax-1cn
    c1
    vx
    divrcnv
    mp1i
    rlimadd
    eqbrtrd
    00id
    syl6breq
    @15
    @8
    @15
    @7
    @0
    @15
    @21
    @7
    cr
    wcel
    #
    @22
    @1
    peano2re
    #
    syl
    @26
    rerpdivcld
    recnd
    #
    @15
    @1
    @5
    @23
    @15
    @5
    @15
    @4
    @0
    @15
    @3
    crp
    wcel
    @4
    cr
    wcel
    @15
    @3
    @15
    @0
    cr
    wcel
    #
    cc0
    @0
    cle
    wbr
    wa
    #
    @2
    cn0
    wcel
    @3
    cn
    wcel
    @14
    @35
    wtru
    @0
    rprege0
    #
    adantl
    @0
    flge0nn0
    @2
    faccl
    3syl
    nnrpd
    @3
    relogcl
    syl
    #
    @26
    rerpdivcld
    recnd
    #
    subcld
    wtru
    @14
    c1
    @0
    cle
    wbr
    #
    wa
    #
    wa
    #
    @4
    @0
    @1
    c1
    cmin
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @0
    cdiv
    co
    #
    @8
    @6
    c1
    cmin
    co
    #
    cabs
    cfv
    #
    @8
    cc0
    cmin
    co
    #
    cabs
    cfv
    #
    cle
    @41
    @45
    @7
    cle
    wbr
    #
    @46
    @8
    cle
    wbr
    #
    @40
    @51
    wtru
    @0
    logfacbnd3
    adantl
    @41
    @45
    cr
    wcel
    @31
    @34
    cc0
    @0
    clt
    wbr
    wa
    #
    @51
    @52
    wb
    @41
    @44
    @41
    @4
    @43
    wtru
    @14
    @4
    cc
    wcel
    #
    @39
    @15
    @4
    @37
    recnd
    adantrr
    #
    @41
    @0
    @42
    @41
    @18
    @19
    @14
    @20
    wtru
    @39
    @24
    ad2antrl
    #
    simpld
    #
    @41
    @16
    @17
    @42
    cc
    wcel
    wtru
    @14
    @16
    @39
    @23
    adantrr
    #
    ax-1cn
    @1
    c1
    subcl
    sylancl
    #
    mulcld
    #
    subcld
    abscld
    @41
    @21
    @31
    wtru
    @14
    @21
    @39
    @22
    adantrr
    #
    @32
    syl
    @14
    @53
    wtru
    @39
    @0
    rpregt0
    ad2antrl
    @45
    @7
    @0
    lediv1
    syl3anc
    mpbid
    @41
    @48
    @43
    @4
    cmin
    co
    #
    @0
    cdiv
    co
    #
    cabs
    cfv
    @62
    cabs
    cfv
    #
    @0
    cabs
    cfv
    #
    cdiv
    co
    @46
    @41
    @47
    @63
    cabs
    @41
    @43
    @0
    cdiv
    co
    #
    @5
    cmin
    co
    #
    @42
    @5
    cmin
    co
    @63
    @47
    @41
    @66
    @42
    @5
    cmin
    @41
    @42
    @0
    @59
    @57
    @41
    @18
    @19
    @56
    simprd
    #
    divcan3d
    oveq1d
    @41
    @43
    cc
    wcel
    @54
    @20
    @63
    @67
    wceq
    @60
    @55
    @56
    @43
    @4
    @0
    divsubdir
    syl3anc
    @41
    @1
    @5
    c1
    @58
    wtru
    @14
    @5
    cc
    wcel
    @39
    @38
    adantrr
    @41
    1cnd
    sub32d
    3eqtr4rd
    fveq2d
    @41
    @62
    @0
    @41
    @43
    @4
    @60
    @55
    subcld
    @57
    @68
    absdivd
    @41
    @64
    @45
    @65
    @0
    cdiv
    @41
    @43
    @4
    @60
    @55
    abssubd
    @41
    @35
    @65
    @0
    wceq
    @14
    @35
    wtru
    @39
    @36
    ad2antrl
    @0
    absid
    syl
    oveq12d
    3eqtrd
    @41
    @50
    @8
    cabs
    cfv
    #
    @8
    @41
    @49
    @8
    cabs
    @41
    @8
    wtru
    @14
    @8
    cc
    wcel
    @39
    @33
    adantrr
    subid1d
    fveq2d
    @41
    @8
    crp
    wcel
    @8
    cr
    wcel
    cc0
    @8
    cle
    wbr
    wa
    @69
    @8
    wceq
    @41
    @7
    @0
    @41
    @1
    @61
    @41
    cc0
    c1
    clog
    cfv
    #
    @1
    cle
    log1
    @41
    @39
    @70
    @1
    cle
    wbr
    #
    wtru
    @14
    @39
    simprr
    @41
    @30
    @14
    @39
    @71
    wb
    1rp
    wtru
    @14
    @14
    @39
    @26
    adantrr
    #
    c1
    @0
    logleb
    sylancr
    mpbid
    syl5eqbrr
    ge0p1rpd
    @72
    rpdivcld
    @8
    rprege0
    @8
    absid
    3syl
    eqtrd
    3brtr4d
    rlimsqzlem
    trud
end
