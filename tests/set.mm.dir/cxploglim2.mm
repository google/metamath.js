include "cc.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cv.mm"
include "clog.mm"
include "cfv.mm"
include "c1.mm"
include "cre.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cdiv.mm"
include "co.mm"
include "ccxp.mm"
include "cc0.mm"
include "c3.mm"
include "cr.mm"
include "3re.mm"
include "a1i.mm"
include "0red.mm"
include "recnd.mm"
include "cvv.mm"
include "ovexd.mm"
include "cmpt.mm"
include "crli.mm"
include "simpr.mm"
include "recl.mm"
include "adantr.mm"
include "1re.mm"
include "ifcl.mm"
include "sylancl.mm"
include "clt.mm"
include "0lt1.mm"
include "max1.mm"
include "sylancr.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "rpdivcld.mm"
include "cxploglim.mm"
include "syl.mm"
include "rlimcxp.mm"
include "rlimmptrcl.mm"
include "cxpcld.mm"
include "relogcl.mm"
include "adantl.mm"
include "simpll.mm"
include "rpre.mm"
include "ad2antlr.mm"
include "rpcxpcld.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "divcld.mm"
include "cabs.mm"
include "cmin.mm"
include "adantrr.mm"
include "abscld.mm"
include "ad2antrl.mm"
include "1lt3.mm"
include "simprr.mm"
include "rplogcld.mm"
include "rerpdivcld.mm"
include "rpred.mm"
include "wceq.mm"
include "abscxp.mm"
include "syl2anc.mm"
include "recld.mm"
include "max2.mm"
include "ceu.mm"
include "loge.mm"
include "ere.mm"
include "c2.mm"
include "egt2lt3.mm"
include "simpri.mm"
include "wb.mm"
include "epr.mm"
include "logltb.mm"
include "mpbid.mm"
include "syl5eqbrr.mm"
include "cxpled.mm"
include "eqbrtrd.mm"
include "lediv1dd.mm"
include "absdivd.mm"
include "rprege0d.mm"
include "absid.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "divcxp.mm"
include "syl3anc.mm"
include "cmul.mm"
include "cxpmuld.mm"
include "divcan1d.mm"
include "eqtr3d.mm"
include "3brtr4d.mm"
include "leabsd.mm"
include "letrd.mm"
include "subid1d.mm"
include "fveq2d.mm"
include "rlimsqzlem.mm"

theorem cxploglim2
  let cA: class A
  let cB: class B
  let vn: setvar n
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint A n
  disjoint B n
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( ( A e. CC /\ B e. RR+ ) -> ( n e. RR+ |-> ( ( ( log ` n ) ^c A ) / ( n ^c B ) ) ) ~~>r 0 )

  proof
    cA
    cc
    wcel
    #
    cB
    crp
    wcel
    #
    wa
    #
    vn
    crp
    vn
    cv
    #
    clog
    cfv
    #
    @3
    cB
    c1
    cA
    cre
    cfv
    #
    cle
    wbr
    #
    @5
    c1
    cif
    #
    cdiv
    co
    #
    ccxp
    co
    #
    cdiv
    co
    #
    @7
    ccxp
    co
    #
    @4
    cA
    ccxp
    co
    #
    @3
    cB
    ccxp
    co
    #
    cdiv
    co
    #
    cc0
    cc0
    c3
    c3
    cr
    wcel
    #
    @2
    3re
    a1i
    @2
    cc0
    @2
    0red
    #
    recnd
    @2
    crp
    @10
    @7
    vn
    cvv
    @2
    @3
    crp
    wcel
    #
    wa
    #
    @4
    @9
    cdiv
    ovexd
    #
    @2
    @8
    crp
    wcel
    vn
    crp
    @10
    cmpt
    cc0
    crli
    wbr
    @2
    cB
    @7
    @0
    @1
    simpr
    @2
    @7
    @2
    @5
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @7
    cr
    wcel
    #
    @0
    @20
    @1
    cA
    recl
    adantr
    #
    1re
    @6
    @5
    c1
    cr
    ifcl
    sylancl
    #
    @2
    cc0
    c1
    @7
    @16
    @21
    @2
    1re
    a1i
    @24
    cc0
    c1
    clt
    wbr
    @2
    0lt1
    a1i
    @2
    @21
    @20
    c1
    @7
    cle
    wbr
    1re
    @23
    c1
    @5
    max1
    sylancr
    ltletrd
    elrpd
    #
    rpdivcld
    @8
    vn
    cxploglim
    syl
    #
    @25
    rlimcxp
    @18
    @10
    @7
    @2
    crp
    @10
    cc0
    vn
    cvv
    @19
    @26
    rlimmptrcl
    @18
    @7
    @2
    @22
    @17
    @24
    adantr
    recnd
    cxpcld
    #
    @18
    @12
    @13
    @18
    @4
    cA
    @18
    @4
    @17
    @4
    cr
    wcel
    #
    @2
    @3
    relogcl
    #
    adantl
    recnd
    @0
    @1
    @17
    simpll
    cxpcld
    #
    @18
    @13
    @18
    @3
    cB
    @2
    @17
    simpr
    #
    @1
    cB
    cr
    wcel
    #
    @0
    @17
    cB
    rpre
    #
    ad2antlr
    rpcxpcld
    #
    rpcnd
    #
    @18
    @13
    @34
    rpne0d
    #
    divcld
    #
    @2
    @17
    c3
    @3
    cle
    wbr
    #
    wa
    #
    wa
    #
    @14
    cabs
    cfv
    #
    @11
    cabs
    cfv
    #
    @14
    cc0
    cmin
    co
    #
    cabs
    cfv
    @11
    cc0
    cmin
    co
    #
    cabs
    cfv
    cle
    @40
    @41
    @11
    @42
    @40
    @14
    @2
    @17
    @14
    cc
    wcel
    @38
    @37
    adantrr
    #
    abscld
    @40
    @11
    @40
    @10
    @7
    @40
    @4
    @9
    @40
    @3
    @17
    @3
    cr
    wcel
    @2
    @38
    @3
    rpre
    ad2antrl
    #
    @40
    c1
    c3
    @3
    @21
    @40
    1re
    a1i
    @15
    @40
    3re
    a1i
    #
    @46
    c1
    c3
    clt
    wbr
    @40
    1lt3
    a1i
    @2
    @17
    @38
    simprr
    #
    ltletrd
    rplogcld
    #
    @40
    @3
    @8
    @2
    @17
    @17
    @38
    @31
    adantrr
    #
    @40
    cB
    @7
    @1
    @32
    @0
    @39
    @33
    ad2antlr
    #
    @2
    @7
    crp
    wcel
    @39
    @25
    adantr
    #
    rerpdivcld
    #
    rpcxpcld
    #
    rpdivcld
    @2
    @22
    @39
    @24
    adantr
    #
    rpcxpcld
    rpred
    #
    @40
    @11
    @2
    @17
    @11
    cc
    wcel
    @38
    @27
    adantrr
    #
    abscld
    @40
    @12
    cabs
    cfv
    #
    @13
    cdiv
    co
    #
    @4
    @7
    ccxp
    co
    #
    @13
    cdiv
    co
    #
    @41
    @11
    cle
    @40
    @58
    @60
    @13
    @40
    @12
    @2
    @17
    @12
    cc
    wcel
    @38
    @30
    adantrr
    abscld
    @40
    @60
    @40
    @4
    @7
    @49
    @55
    rpcxpcld
    rpred
    @2
    @17
    @13
    crp
    wcel
    @38
    @34
    adantrr
    #
    @40
    @58
    @4
    @5
    ccxp
    co
    #
    @60
    cle
    @40
    @4
    crp
    wcel
    @0
    @58
    @63
    wceq
    @49
    @0
    @1
    @39
    simpll
    #
    @4
    cA
    abscxp
    syl2anc
    @40
    @5
    @7
    cle
    wbr
    #
    @63
    @60
    cle
    wbr
    @40
    @21
    @20
    @65
    1re
    @40
    cA
    @64
    recld
    #
    c1
    @5
    max2
    sylancr
    @40
    @4
    @5
    @7
    @17
    @28
    @2
    @38
    @29
    ad2antrl
    @40
    c1
    ceu
    clog
    cfv
    #
    @4
    clt
    loge
    @40
    ceu
    @3
    clt
    wbr
    #
    @67
    @4
    clt
    wbr
    #
    @40
    ceu
    c3
    @3
    ceu
    cr
    wcel
    @40
    ere
    a1i
    @47
    @46
    ceu
    c3
    clt
    wbr
    #
    @40
    c2
    ceu
    clt
    wbr
    @70
    egt2lt3
    simpri
    a1i
    @48
    ltletrd
    @40
    ceu
    crp
    wcel
    @17
    @68
    @69
    wb
    epr
    @50
    ceu
    @3
    logltb
    sylancr
    mpbid
    syl5eqbrr
    @66
    @55
    cxpled
    mpbid
    eqbrtrd
    lediv1dd
    @40
    @41
    @58
    @13
    cabs
    cfv
    #
    cdiv
    co
    #
    @59
    @2
    @17
    @41
    @72
    wceq
    @38
    @18
    @12
    @13
    @30
    @35
    @36
    absdivd
    adantrr
    @40
    @71
    @13
    @58
    cdiv
    @40
    @13
    cr
    wcel
    cc0
    @13
    cle
    wbr
    wa
    @71
    @13
    wceq
    @40
    @13
    @62
    rprege0d
    @13
    absid
    syl
    oveq2d
    eqtrd
    @40
    @11
    @60
    @9
    @7
    ccxp
    co
    #
    cdiv
    co
    #
    @61
    @40
    @28
    cc0
    @4
    cle
    wbr
    wa
    @9
    crp
    wcel
    @7
    cc
    wcel
    #
    @11
    @74
    wceq
    @40
    @4
    @49
    rprege0d
    @54
    @2
    @75
    @39
    @2
    @7
    @24
    recnd
    adantr
    #
    @4
    @9
    @7
    divcxp
    syl3anc
    @40
    @73
    @13
    @60
    cdiv
    @40
    @3
    @8
    @7
    cmul
    co
    #
    ccxp
    co
    @73
    @13
    @40
    @3
    @8
    @7
    @50
    @53
    @76
    cxpmuld
    @40
    @77
    cB
    @3
    ccxp
    @40
    cB
    @7
    @40
    cB
    @51
    recnd
    @76
    @40
    @7
    @52
    rpne0d
    divcan1d
    oveq2d
    eqtr3d
    oveq2d
    eqtrd
    3brtr4d
    @40
    @11
    @56
    leabsd
    letrd
    @40
    @43
    @14
    cabs
    @40
    @14
    @45
    subid1d
    fveq2d
    @40
    @44
    @11
    cabs
    @40
    @11
    @57
    subid1d
    fveq2d
    3brtr4d
    rlimsqzlem
end
