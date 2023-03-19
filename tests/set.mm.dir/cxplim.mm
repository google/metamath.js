include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "cv.mm"
include "ccxp.mm"
include "co.mm"
include "cdiv.mm"
include "cmpt.mm"
include "cc0.mm"
include "crli.mm"
include "wbr.mm"
include "clt.mm"
include "cabs.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "wa.mm"
include "cneg.mm"
include "rpre.mm"
include "adantl.mm"
include "cle.mm"
include "rpge0.mm"
include "renegcld.mm"
include "adantr.mm"
include "wne.mm"
include "rpcn.mm"
include "rpne0.mm"
include "negne0d.mm"
include "rereccld.mm"
include "recxpcld.mm"
include "wceq.mm"
include "simprl.mm"
include "ad2antrr.mm"
include "rpcxpcld.mm"
include "rpreccld.mm"
include "rprege0d.mm"
include "absid.mm"
include "syl.mm"
include "simplr.mm"
include "simprr.mm"
include "rpreccl.mm"
include "rpcnd.mm"
include "cxprecd.mm"
include "cc.mm"
include "ad2antlr.mm"
include "cxpnegd.mm"
include "1cnd.mm"
include "divneg2d.mm"
include "oveq2d.mm"
include "3eqtr2d.mm"
include "cmul.mm"
include "recidd.mm"
include "cxpmuld.mm"
include "cxp1d.mm"
include "3eqtr3d.mm"
include "3brtr4d.mm"
include "rpred.mm"
include "rpge0d.mm"
include "cxplt2d.mm"
include "mpbird.mm"
include "ltrec1d.mm"
include "eqbrtrd.mm"
include "expr.mm"
include "ralrimiva.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "id.mm"
include "rpcxpcl.mm"
include "syl2anr.mm"
include "wss.mm"
include "rpssre.mm"
include "a1i.mm"
include "rlim0lt.mm"

theorem cxplim
  let cA: class A
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y

  disjoint A n
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( A e. RR+ -> ( n e. RR+ |-> ( 1 / ( n ^c A ) ) ) ~~>r 0 )

  proof
    cA
    crp
    wcel
    #
    vn
    crp
    c1
    vn
    cv
    #
    cA
    ccxp
    co
    #
    cdiv
    co
    #
    cmpt
    cc0
    crli
    wbr
    vy
    cv
    #
    @1
    clt
    wbr
    #
    @3
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    wi
    #
    vn
    crp
    wral
    #
    vy
    cr
    wrex
    #
    vx
    crp
    wral
    @0
    @11
    vx
    crp
    @0
    @7
    crp
    wcel
    #
    wa
    #
    @7
    c1
    cA
    cneg
    #
    cdiv
    co
    #
    ccxp
    co
    #
    cr
    wcel
    @16
    @1
    clt
    wbr
    #
    @8
    wi
    #
    vn
    crp
    wral
    #
    @11
    @13
    @7
    @15
    @12
    @7
    cr
    wcel
    @0
    @7
    rpre
    adantl
    @12
    cc0
    @7
    cle
    wbr
    @0
    @7
    rpge0
    adantl
    @13
    @14
    @0
    @14
    cr
    wcel
    @12
    @0
    cA
    cA
    rpre
    #
    renegcld
    adantr
    @0
    @14
    cc0
    wne
    @12
    @0
    cA
    cA
    rpcn
    #
    cA
    rpne0
    #
    negne0d
    adantr
    rereccld
    recxpcld
    @13
    @18
    vn
    crp
    @13
    @1
    crp
    wcel
    #
    @17
    @8
    @13
    @23
    @17
    wa
    #
    wa
    #
    @6
    @3
    @7
    clt
    @25
    @3
    cr
    wcel
    cc0
    @3
    cle
    wbr
    wa
    @6
    @3
    wceq
    @25
    @3
    @25
    @2
    @25
    @1
    cA
    @13
    @23
    @17
    simprl
    #
    @0
    cA
    cr
    wcel
    #
    @12
    @24
    @20
    ad2antrr
    #
    rpcxpcld
    #
    rpreccld
    rprege0d
    @3
    absid
    syl
    @25
    @7
    @2
    @0
    @12
    @24
    simplr
    #
    @29
    @25
    c1
    @7
    cdiv
    co
    #
    @2
    clt
    wbr
    @31
    c1
    cA
    cdiv
    co
    #
    ccxp
    co
    #
    @2
    @32
    ccxp
    co
    #
    clt
    wbr
    @25
    @16
    @1
    @33
    @34
    clt
    @13
    @23
    @17
    simprr
    @25
    @33
    c1
    @7
    @32
    ccxp
    co
    cdiv
    co
    @7
    @32
    cneg
    #
    ccxp
    co
    @16
    @25
    @7
    @32
    @30
    @25
    @32
    @0
    @32
    crp
    wcel
    @12
    @24
    cA
    rpreccl
    ad2antrr
    #
    rpcnd
    #
    cxprecd
    @25
    @7
    @32
    @12
    @7
    cc
    wcel
    @0
    @24
    @7
    rpcn
    ad2antlr
    @12
    @7
    cc0
    wne
    @0
    @24
    @7
    rpne0
    ad2antlr
    @37
    cxpnegd
    @25
    @35
    @15
    @7
    ccxp
    @25
    c1
    cA
    @25
    1cnd
    @0
    cA
    cc
    wcel
    @12
    @24
    @21
    ad2antrr
    #
    @0
    cA
    cc0
    wne
    @12
    @24
    @22
    ad2antrr
    #
    divneg2d
    oveq2d
    3eqtr2d
    @25
    @1
    cA
    @32
    cmul
    co
    #
    ccxp
    co
    @1
    c1
    ccxp
    co
    @34
    @1
    @25
    @40
    c1
    @1
    ccxp
    @25
    cA
    @38
    @39
    recidd
    oveq2d
    @25
    @1
    cA
    @32
    @26
    @28
    @37
    cxpmuld
    @25
    @1
    @25
    @1
    @26
    rpcnd
    cxp1d
    3eqtr3d
    3brtr4d
    @25
    @31
    @2
    @32
    @25
    @31
    @12
    @31
    crp
    wcel
    @0
    @24
    @7
    rpreccl
    ad2antlr
    #
    rpred
    @25
    @31
    @41
    rpge0d
    @25
    @2
    @29
    rpred
    @25
    @2
    @29
    rpge0d
    @36
    cxplt2d
    mpbird
    ltrec1d
    eqbrtrd
    expr
    ralrimiva
    @10
    @19
    vy
    @16
    cr
    @4
    @16
    wceq
    #
    @9
    @18
    vn
    crp
    @42
    @5
    @17
    @8
    @4
    @16
    @1
    clt
    breq1
    imbi1d
    ralbidv
    rspcev
    syl2anc
    ralrimiva
    @0
    vx
    vy
    vn
    crp
    @3
    @0
    @3
    cc
    wcel
    vn
    crp
    @0
    @23
    wa
    #
    @3
    @43
    @2
    @23
    @23
    @27
    @2
    crp
    wcel
    @0
    @23
    id
    @20
    @1
    cA
    rpcxpcl
    syl2anr
    rpreccld
    rpcnd
    ralrimiva
    crp
    cr
    wss
    @0
    rpssre
    a1i
    rlim0lt
    mpbird
end
