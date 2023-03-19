include "cn.mm"
include "wcel.mm"
include "caddc.mm"
include "cc0.mm"
include "cseq.mm"
include "c1.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "cmin.mm"
include "clog.mm"
include "cfv.mm"
include "cli.mm"
include "cneg.mm"
include "cv.mm"
include "cexp.mm"
include "cmpt.mm"
include "cn0.mm"
include "eqid.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "nnre.mm"
include "remulcld.mm"
include "cle.mm"
include "wbr.mm"
include "0le2.mm"
include "0red.mm"
include "nngt0.mm"
include "ltled.mm"
include "mulge0d.mm"
include "ge0p1rpd.mm"
include "rpreccld.mm"
include "cabs.mm"
include "clt.mm"
include "1red.mm"
include "renegcld.mm"
include "rpred.mm"
include "neg1lt0.mm"
include "rpgt0d.mm"
include "lttrd.mm"
include "crp.mm"
include "1rp.mm"
include "1cnd.mm"
include "div1d.mm"
include "2rp.mm"
include "nnrp.mm"
include "rpmulcld.mm"
include "ltaddrp2d.mm"
include "eqbrtrd.mm"
include "ltrec1d.mm"
include "absltd.mm"
include "mpbir2and.mm"
include "stirlinglem5.mm"
include "2cnd.mm"
include "nncn.mm"
include "mulcld.mm"
include "addcld.mm"
include "readdcld.mm"
include "2pos.mm"
include "mulgt0d.mm"
include "ltp1d.mm"
include "gt0ne0d.mm"
include "dividd.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "divdird.mm"
include "divsubdird.mm"
include "addassd.mm"
include "wceq.mm"
include "1p1e2.mm"
include "oveq2d.mm"
include "mulid1d.mm"
include "adddid.mm"
include "eqtr4d.mm"
include "3eqtrd.mm"
include "pncand.mm"
include "eqtrd.mm"
include "divcan7d.mm"
include "divmuldivd.mm"
include "divcld.mm"
include "mulid2d.mm"
include "fveq2d.mm"
include "breqtrd.mm"

theorem stirlinglem6
  let vj: setvar j
  let cH: class H
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  assume stirlinglem6.1: |- H = ( j e. NN0 |-> ( 2 x. ( ( 1 / ( ( 2 x. j ) + 1 ) ) x. ( ( 1 / ( ( 2 x. N ) + 1 ) ) ^ ( ( 2 x. j ) + 1 ) ) ) ) )

  disjoint N j
  disjoint k x
  assert |- ( N e. NN -> seq 0 ( + , H ) ~~> ( log ` ( ( N + 1 ) / N ) ) )

  proof
    cN
    cn
    wcel
    #
    caddc
    cH
    cc0
    cseq
    c1
    c1
    c2
    cN
    cmul
    co
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    caddc
    co
    #
    c1
    @3
    cmin
    co
    #
    cdiv
    co
    #
    clog
    cfv
    cN
    c1
    caddc
    co
    #
    cN
    cdiv
    co
    #
    clog
    cfv
    cli
    @0
    vj
    cn
    c1
    cneg
    #
    vj
    cv
    #
    c1
    cmin
    co
    cexp
    co
    @3
    @10
    cexp
    co
    @10
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    #
    @3
    vj
    vj
    cn
    @11
    cmpt
    #
    vj
    cn
    @12
    @11
    caddc
    co
    cmpt
    #
    vj
    cn0
    c2
    @10
    cmul
    co
    c1
    caddc
    co
    cmpt
    #
    cH
    @13
    eqid
    @14
    eqid
    @15
    eqid
    stirlinglem6.1
    @16
    eqid
    @0
    @2
    @0
    @1
    @0
    c2
    cN
    c2
    cr
    wcel
    @0
    2re
    a1i
    #
    cN
    nnre
    #
    remulcld
    #
    @0
    c2
    cN
    @17
    @18
    cc0
    c2
    cle
    wbr
    @0
    0le2
    a1i
    @0
    cc0
    cN
    @0
    0red
    #
    @18
    cN
    nngt0
    #
    ltled
    mulge0d
    ge0p1rpd
    #
    rpreccld
    #
    @0
    @3
    cabs
    cfv
    c1
    clt
    wbr
    @9
    @3
    clt
    wbr
    @3
    c1
    clt
    wbr
    @0
    @9
    cc0
    @3
    @0
    c1
    @0
    1red
    #
    renegcld
    @20
    @0
    @3
    @23
    rpred
    #
    @9
    cc0
    clt
    wbr
    @0
    neg1lt0
    a1i
    @0
    @3
    @23
    rpgt0d
    lttrd
    @0
    c1
    @2
    c1
    crp
    wcel
    @0
    1rp
    a1i
    @22
    @0
    c1
    c1
    cdiv
    co
    c1
    @2
    clt
    @0
    c1
    @0
    1cnd
    #
    div1d
    @0
    c1
    @1
    @24
    @0
    c2
    cN
    c2
    crp
    wcel
    @0
    2rp
    a1i
    cN
    nnrp
    rpmulcld
    ltaddrp2d
    eqbrtrd
    ltrec1d
    @0
    @3
    c1
    @25
    @24
    absltd
    mpbir2and
    stirlinglem5
    @0
    @6
    @8
    clog
    @0
    @6
    @2
    @2
    cdiv
    co
    #
    @3
    caddc
    co
    #
    @27
    @3
    cmin
    co
    #
    cdiv
    co
    #
    c2
    @7
    cmul
    co
    #
    @2
    cdiv
    co
    #
    @1
    @2
    cdiv
    co
    #
    cdiv
    co
    #
    @8
    @0
    @4
    @28
    @5
    @29
    cdiv
    @0
    c1
    @27
    @3
    caddc
    @0
    @27
    c1
    @0
    @2
    @0
    @1
    c1
    @0
    c2
    cN
    @0
    2cnd
    #
    cN
    nncn
    #
    mulcld
    #
    @26
    addcld
    #
    @0
    @2
    @0
    cc0
    @1
    @2
    @20
    @19
    @0
    @1
    c1
    @19
    @24
    readdcld
    @0
    c2
    cN
    @17
    @18
    cc0
    c2
    clt
    wbr
    @0
    2pos
    a1i
    #
    @21
    mulgt0d
    #
    @0
    @1
    @19
    ltp1d
    lttrd
    gt0ne0d
    #
    dividd
    eqcomd
    #
    oveq1d
    @0
    c1
    @27
    @3
    cmin
    @42
    oveq1d
    oveq12d
    @0
    @30
    @2
    c1
    caddc
    co
    #
    @2
    cdiv
    co
    #
    @2
    c1
    cmin
    co
    #
    @2
    cdiv
    co
    #
    cdiv
    co
    @34
    @0
    @28
    @44
    @29
    @46
    cdiv
    @0
    @44
    @28
    @0
    @2
    c1
    @2
    @38
    @26
    @38
    @41
    divdird
    eqcomd
    @0
    @46
    @29
    @0
    @2
    c1
    @2
    @38
    @26
    @38
    @41
    divsubdird
    eqcomd
    oveq12d
    @0
    @44
    @32
    @46
    @33
    cdiv
    @0
    @43
    @31
    @2
    cdiv
    @0
    @43
    @1
    c1
    c1
    caddc
    co
    #
    caddc
    co
    @1
    c2
    caddc
    co
    #
    @31
    @0
    @1
    c1
    c1
    @37
    @26
    @26
    addassd
    @0
    @47
    c2
    @1
    caddc
    @47
    c2
    wceq
    @0
    1p1e2
    a1i
    oveq2d
    @0
    @48
    @1
    c2
    c1
    cmul
    co
    #
    caddc
    co
    @31
    @0
    c2
    @49
    @1
    caddc
    @0
    @49
    c2
    @0
    c2
    @35
    mulid1d
    eqcomd
    oveq2d
    @0
    c2
    cN
    c1
    @35
    @36
    @26
    adddid
    eqtr4d
    3eqtrd
    oveq1d
    @0
    @45
    @1
    @2
    cdiv
    @0
    @1
    c1
    @37
    @26
    pncand
    oveq1d
    oveq12d
    eqtrd
    @0
    @34
    @31
    @1
    cdiv
    co
    #
    c2
    c2
    cdiv
    co
    #
    @8
    cmul
    co
    #
    @8
    @0
    @31
    @1
    @2
    @0
    c2
    @7
    @35
    @0
    cN
    c1
    @36
    @26
    addcld
    #
    mulcld
    @37
    @38
    @0
    @1
    @40
    gt0ne0d
    @41
    divcan7d
    @0
    @52
    @50
    @0
    c2
    c2
    @7
    cN
    @35
    @35
    @53
    @36
    @0
    c2
    @39
    gt0ne0d
    #
    @0
    cN
    @21
    gt0ne0d
    #
    divmuldivd
    eqcomd
    @0
    @52
    c1
    @8
    cmul
    co
    @8
    @0
    @51
    c1
    @8
    cmul
    @0
    c2
    @35
    @54
    dividd
    oveq1d
    @0
    @8
    @0
    @7
    cN
    @53
    @36
    @55
    divcld
    mulid2d
    eqtrd
    3eqtrd
    3eqtrd
    fveq2d
    breqtrd
end
