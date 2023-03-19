include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cdiv.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "cmul.mm"
include "cle.mm"
include "cif.mm"
include "c2.mm"
include "1rp.mm"
include "wne.mm"
include "simpl.mm"
include "eldifsn.mm"
include "sylib.mm"
include "absrpcl.mm"
include "syl.mm"
include "rpmulcl.mm"
include "sylancom.mm"
include "ifcl.mm"
include "sylancr.mm"
include "rphalfcld.mm"
include "rpmulcld.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "simpld.mm"
include "simprl.mm"
include "mulcld.mm"
include "mulne0.mm"
include "syl2anc.mm"
include "divsubdird.mm"
include "mulid1d.mm"
include "oveq1d.mm"
include "wceq.mm"
include "1cnd.mm"
include "divcan5.mm"
include "syl3anc.mm"
include "eqtr3d.mm"
include "mulcomd.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "subcld.mm"
include "absdivd.mm"
include "cr.mm"
include "abssubd.mm"
include "abscld.mm"
include "eqeltrd.mm"
include "rpred.mm"
include "rpre.mm"
include "ad2antlr.mm"
include "remulcld.mm"
include "simprr.mm"
include "eqbrtrd.mm"
include "1re.mm"
include "min2.mm"
include "lemul1d.mm"
include "mpbid.mm"
include "syl5eqbr.mm"
include "caddc.mm"
include "recnd.mm"
include "2halvesd.mm"
include "resubcld.mm"
include "abs2difd.mm"
include "min1.mm"
include "1red.mm"
include "mulid2d.mm"
include "breqtrd.mm"
include "ltletrd.mm"
include "lelttrd.mm"
include "ltsubadd2d.mm"
include "ltadd1d.mm"
include "mpbird.mm"
include "ltmul2dd.mm"
include "absmuld.mm"
include "mul32d.mm"
include "breqtrrd.mm"
include "lttrd.mm"
include "absrpcld.mm"
include "ltdivmuld.mm"
include "expr.mm"
include "ralrimiva.mm"
include "breq2.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"

theorem reccn2
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cT: class T
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cC: class C
  assume reccn2.t: |- T = ( if ( 1 <_ ( ( abs ` A ) x. B ) , 1 , ( ( abs ` A ) x. B ) ) x. ( ( abs ` A ) / 2 ) )

  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint T y
  disjoint T z
  disjoint u v
  disjoint u w
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint C u
  disjoint C v
  disjoint C w
  disjoint C y
  disjoint C z
  assert |- ( ( A e. ( CC \ { 0 } ) /\ B e. RR+ ) -> E. y e. RR+ A. z e. ( CC \ { 0 } ) ( ( abs ` ( z - A ) ) < y -> ( abs ` ( ( 1 / z ) - ( 1 / A ) ) ) < B ) )

  proof
    cA
    cc
    cc0
    csn
    cdif
    #
    wcel
    #
    cB
    crp
    wcel
    #
    wa
    #
    cT
    crp
    wcel
    #
    vz
    cv
    #
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    cT
    clt
    wbr
    #
    c1
    @5
    cdiv
    co
    #
    c1
    cA
    cdiv
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cB
    clt
    wbr
    #
    wi
    #
    vz
    @0
    wral
    #
    @7
    vy
    cv
    #
    clt
    wbr
    #
    @13
    wi
    #
    vz
    @0
    wral
    #
    vy
    crp
    wrex
    @3
    cT
    c1
    cA
    cabs
    cfv
    #
    cB
    cmul
    co
    #
    cle
    wbr
    #
    c1
    @21
    cif
    #
    @20
    c2
    cdiv
    co
    #
    cmul
    co
    #
    crp
    reccn2.t
    @3
    @23
    @24
    @3
    c1
    crp
    wcel
    @21
    crp
    wcel
    #
    @23
    crp
    wcel
    #
    1rp
    @1
    @2
    @20
    crp
    wcel
    #
    @26
    @3
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    @28
    @3
    @1
    @31
    @1
    @2
    simpl
    cA
    cc
    cc0
    eldifsn
    sylib
    #
    cA
    absrpcl
    syl
    #
    @20
    cB
    rpmulcl
    sylancom
    #
    @22
    c1
    @21
    crp
    ifcl
    sylancr
    #
    @3
    @20
    @33
    rphalfcld
    #
    rpmulcld
    syl5eqel
    #
    @3
    @14
    vz
    @0
    @3
    @5
    @0
    wcel
    #
    @8
    @13
    @3
    @38
    @8
    wa
    #
    wa
    #
    @12
    cA
    @5
    cmin
    co
    #
    cabs
    cfv
    #
    cA
    @5
    cmul
    co
    #
    cabs
    cfv
    #
    cdiv
    co
    #
    cB
    clt
    @40
    @41
    @43
    cdiv
    co
    #
    cabs
    cfv
    @12
    @45
    @40
    @46
    @11
    cabs
    @40
    @46
    cA
    @43
    cdiv
    co
    #
    @5
    @43
    cdiv
    co
    #
    cmin
    co
    @11
    @40
    cA
    @5
    @43
    @40
    @29
    @30
    @3
    @31
    @39
    @32
    adantr
    #
    simpld
    #
    @40
    @5
    cc
    wcel
    #
    @5
    cc0
    wne
    #
    @40
    @38
    @51
    @52
    wa
    #
    @3
    @38
    @8
    simprl
    @5
    cc
    cc0
    eldifsn
    sylib
    #
    simpld
    #
    @40
    cA
    @5
    @50
    @55
    mulcld
    #
    @40
    @31
    @53
    @43
    cc0
    wne
    @49
    @54
    cA
    @5
    mulne0
    syl2anc
    #
    divsubdird
    @40
    @47
    @9
    @48
    @10
    cmin
    @40
    cA
    c1
    cmul
    co
    #
    @43
    cdiv
    co
    #
    @47
    @9
    @40
    @58
    cA
    @43
    cdiv
    @40
    cA
    @50
    mulid1d
    oveq1d
    @40
    c1
    cc
    wcel
    #
    @53
    @31
    @59
    @9
    wceq
    @40
    1cnd
    #
    @54
    @49
    c1
    @5
    cA
    divcan5
    syl3anc
    eqtr3d
    @40
    @5
    c1
    cmul
    co
    #
    @5
    cA
    cmul
    co
    #
    cdiv
    co
    #
    @48
    @10
    @40
    @62
    @5
    @63
    @43
    cdiv
    @40
    @5
    @55
    mulid1d
    @40
    @5
    cA
    @55
    @50
    mulcomd
    oveq12d
    @40
    @60
    @31
    @53
    @64
    @10
    wceq
    @61
    @49
    @54
    c1
    cA
    @5
    divcan5
    syl3anc
    eqtr3d
    oveq12d
    eqtrd
    fveq2d
    @40
    @41
    @43
    @40
    cA
    @5
    @50
    @55
    subcld
    @56
    @57
    absdivd
    eqtr3d
    @40
    @45
    cB
    clt
    wbr
    @42
    @44
    cB
    cmul
    co
    #
    clt
    wbr
    @40
    @42
    cT
    @65
    @40
    @42
    @7
    cr
    @40
    cA
    @5
    @50
    @55
    abssubd
    #
    @40
    @6
    @40
    @5
    cA
    @55
    @50
    subcld
    abscld
    eqeltrd
    #
    @40
    cT
    @3
    @4
    @39
    @37
    adantr
    rpred
    #
    @40
    @44
    cB
    @40
    @43
    @56
    abscld
    @2
    cB
    cr
    wcel
    @1
    @39
    cB
    rpre
    ad2antlr
    #
    remulcld
    #
    @40
    @42
    @7
    cT
    clt
    @66
    @3
    @38
    @8
    simprr
    eqbrtrd
    #
    @40
    cT
    @21
    @24
    cmul
    co
    #
    @65
    @68
    @40
    @21
    @24
    @40
    @21
    @3
    @26
    @39
    @34
    adantr
    #
    rpred
    #
    @40
    @24
    @3
    @24
    crp
    wcel
    @39
    @36
    adantr
    #
    rpred
    #
    remulcld
    @70
    @40
    cT
    @25
    @72
    cle
    reccn2.t
    @40
    @23
    @21
    cle
    wbr
    #
    @25
    @72
    cle
    wbr
    @40
    c1
    cr
    wcel
    #
    @21
    cr
    wcel
    #
    @77
    1re
    @74
    c1
    @21
    min2
    sylancr
    @40
    @23
    @21
    @24
    @40
    @23
    @3
    @27
    @39
    @35
    adantr
    rpred
    #
    @74
    @75
    lemul1d
    mpbid
    syl5eqbr
    @40
    @72
    @21
    @5
    cabs
    cfv
    #
    cmul
    co
    #
    @65
    clt
    @40
    @24
    @81
    @21
    @76
    @40
    @5
    @55
    abscld
    #
    @73
    @40
    @24
    @81
    clt
    wbr
    @24
    @24
    caddc
    co
    #
    @81
    @24
    caddc
    co
    #
    clt
    wbr
    @40
    @84
    @20
    @85
    clt
    @40
    @20
    @40
    @20
    @40
    cA
    @50
    abscld
    #
    recnd
    #
    2halvesd
    @40
    @20
    @81
    cmin
    co
    #
    @24
    clt
    wbr
    @20
    @85
    clt
    wbr
    @40
    @88
    @42
    @24
    @40
    @20
    @81
    @86
    @83
    resubcld
    @67
    @76
    @40
    cA
    @5
    @50
    @55
    abs2difd
    @40
    @42
    cT
    @24
    @67
    @68
    @76
    @71
    @40
    cT
    c1
    @24
    cmul
    co
    #
    @24
    cle
    @40
    cT
    @25
    @89
    cle
    reccn2.t
    @40
    @23
    c1
    cle
    wbr
    #
    @25
    @89
    cle
    wbr
    @40
    @78
    @79
    @90
    1re
    @74
    c1
    @21
    min1
    sylancr
    @40
    @23
    c1
    @24
    @80
    @40
    1red
    @75
    lemul1d
    mpbid
    syl5eqbr
    @40
    @24
    @40
    @24
    @76
    recnd
    mulid2d
    breqtrd
    ltletrd
    lelttrd
    @40
    @20
    @81
    @24
    @86
    @83
    @76
    ltsubadd2d
    mpbid
    eqbrtrd
    @40
    @24
    @81
    @24
    @76
    @83
    @76
    ltadd1d
    mpbird
    ltmul2dd
    @40
    @65
    @20
    @81
    cmul
    co
    #
    cB
    cmul
    co
    @82
    @40
    @44
    @91
    cB
    cmul
    @40
    cA
    @5
    @50
    @55
    absmuld
    oveq1d
    @40
    @20
    @81
    cB
    @87
    @40
    @81
    @83
    recnd
    @40
    cB
    @69
    recnd
    mul32d
    eqtrd
    breqtrrd
    lelttrd
    lttrd
    @40
    @42
    cB
    @44
    @67
    @69
    @40
    @43
    @56
    @57
    absrpcld
    ltdivmuld
    mpbird
    eqbrtrd
    expr
    ralrimiva
    @19
    @15
    vy
    cT
    crp
    @16
    cT
    wceq
    #
    @18
    @14
    vz
    @0
    @92
    @17
    @8
    @13
    @16
    cT
    @7
    clt
    breq2
    imbi1d
    ralbidv
    rspcev
    syl2anc
end
