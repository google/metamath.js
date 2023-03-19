include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "w3a.mm"
include "ci.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "cneg.mm"
include "wceq.mm"
include "wo.mm"
include "cpr.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cdiv.mm"
include "c2.mm"
include "2cn.mm"
include "picn.mm"
include "mulcli.mm"
include "2ne0.mm"
include "divreci.mm"
include "divcan3i.mm"
include "eqtr3i.mm"
include "cmin.mm"
include "cle.mm"
include "caddc.mm"
include "ang180lem2.mm"
include "simprd.mm"
include "1e0p1.mm"
include "syl6breq.mm"
include "cz.mm"
include "wb.mm"
include "cr.mm"
include "ang180lem1.mm"
include "simpld.mm"
include "0z.mm"
include "zleltp1.mm"
include "sylancl.mm"
include "mpbird.mm"
include "adantr.mm"
include "zlem1lt.mm"
include "sylancr.mm"
include "df-neg.mm"
include "breq1i.mm"
include "syl6bbr.mm"
include "biimpar.mm"
include "zred.mm"
include "0re.mm"
include "letri3.mm"
include "mpbir2and.mm"
include "syl5eqr.mm"
include "clog.mm"
include "cfv.mm"
include "ax-1cn.mm"
include "simp1.mm"
include "subcl.mm"
include "simp3.mm"
include "necomd.mm"
include "subeq0.mm"
include "necon3bid.mm"
include "reccld.mm"
include "recne0d.mm"
include "logcld.mm"
include "simp2.mm"
include "divcld.mm"
include "divne0d.mm"
include "addcld.mm"
include "logcl.mm"
include "3adant3.mm"
include "syl5eqel.mm"
include "ax-icn.mm"
include "a1i.mm"
include "ine0.mm"
include "pire.mm"
include "pipos.mm"
include "gt0ne0ii.mm"
include "mulne0i.mm"
include "halfcn.mm"
include "mpbid.mm"
include "divmuld.mm"
include "syl5reqr.mm"
include "eqcomd.mm"
include "olcd.mm"
include "mulneg1i.mm"
include "mulcomi.mm"
include "negeqi.mm"
include "eqtri.mm"
include "divcan1i.mm"
include "oveq1i.mm"
include "mulassi.mm"
include "mulid2i.mm"
include "3eqtr3i.mm"
include "negsubdii.mm"
include "1mhlfehlf.mm"
include "simpr.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "npcan.mm"
include "eqtrd.mm"
include "divcan1d.mm"
include "eqtr2d.mm"
include "orcd.mm"
include "df-2.mm"
include "negdi2.mm"
include "mp2an.mm"
include "syl5eqbrr.mm"
include "neg1z.mm"
include "neg1rr.mm"
include "leloe.mm"
include "mpjaodan.mm"
include "cvv.mm"
include "ovex.mm"
include "eqeltri.mm"
include "elpr.mm"
include "sylibr.mm"

theorem ang180lem3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cT: class T
  let cF: class F
  let cN: class N
  let cB: class B
  let cC: class C
  assume ang.1: |- F = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } ) |-> ( Im ` ( log ` ( y / x ) ) ) )
  assume ang180lem1.2: |- T = ( ( ( log ` ( 1 / ( 1 - A ) ) ) + ( log ` ( ( A - 1 ) / A ) ) ) + ( log ` A ) )
  assume ang180lem1.3: |- N = ( ( ( T / _i ) / ( 2 x. _pi ) ) - ( 1 / 2 ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  assert |- ( ( A e. CC /\ A =/= 0 /\ A =/= 1 ) -> T e. { -u ( _i x. _pi ) , ( _i x. _pi ) } )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cA
    c1
    wne
    #
    w3a
    #
    cT
    ci
    cpi
    cmul
    co
    #
    cneg
    #
    wceq
    #
    cT
    @4
    wceq
    #
    wo
    #
    cT
    @5
    @4
    cpr
    wcel
    @3
    c1
    cneg
    #
    cN
    clt
    wbr
    #
    @8
    @9
    cN
    wceq
    #
    @3
    @10
    wa
    #
    @7
    @6
    @12
    @4
    cT
    @12
    cT
    ci
    cdiv
    co
    #
    cpi
    wceq
    @4
    cT
    wceq
    @12
    cpi
    c2
    cpi
    cmul
    co
    #
    c1
    c2
    cdiv
    co
    #
    cmul
    co
    #
    @13
    @14
    c2
    cdiv
    co
    @16
    cpi
    @14
    c2
    c2
    cpi
    2cn
    picn
    mulcli
    #
    2cn
    2ne0
    divreci
    cpi
    c2
    picn
    2cn
    2ne0
    divcan3i
    eqtr3i
    @12
    @13
    @14
    cdiv
    co
    #
    @15
    wceq
    #
    @16
    @13
    wceq
    @12
    @18
    @15
    cmin
    co
    #
    cc0
    wceq
    #
    @19
    @12
    @20
    cN
    cc0
    ang180lem1.3
    @12
    cN
    cc0
    wceq
    #
    cN
    cc0
    cle
    wbr
    #
    cc0
    cN
    cle
    wbr
    #
    @3
    @23
    @10
    @3
    @23
    cN
    cc0
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @3
    cN
    c1
    @25
    clt
    @3
    c2
    cneg
    #
    cN
    clt
    wbr
    #
    cN
    c1
    clt
    wbr
    #
    vx
    vy
    cA
    cT
    cF
    cN
    ang.1
    ang180lem1.2
    ang180lem1.3
    ang180lem2
    #
    simprd
    1e0p1
    syl6breq
    @3
    cN
    cz
    wcel
    #
    cc0
    cz
    wcel
    #
    @23
    @26
    wb
    @3
    @31
    @13
    cr
    wcel
    vx
    vy
    cA
    cT
    cF
    cN
    ang.1
    ang180lem1.2
    ang180lem1.3
    ang180lem1
    simpld
    #
    0z
    cN
    cc0
    zleltp1
    sylancl
    mpbird
    adantr
    @3
    @24
    @10
    @3
    @24
    cc0
    c1
    cmin
    co
    #
    cN
    clt
    wbr
    #
    @10
    @3
    @32
    @31
    @24
    @35
    wb
    0z
    @33
    cc0
    cN
    zlem1lt
    sylancr
    @9
    @34
    cN
    clt
    c1
    df-neg
    breq1i
    syl6bbr
    biimpar
    @12
    cN
    cr
    wcel
    #
    cc0
    cr
    wcel
    @22
    @23
    @24
    wa
    wb
    @3
    @36
    @10
    @3
    cN
    @33
    zred
    #
    adantr
    0re
    cN
    cc0
    letri3
    sylancl
    mpbir2and
    syl5eqr
    @12
    @18
    cc
    wcel
    #
    @15
    cc
    wcel
    #
    @21
    @19
    wb
    @3
    @38
    @10
    @3
    @13
    @14
    @3
    cT
    ci
    @3
    cT
    c1
    c1
    cA
    cmin
    co
    #
    cdiv
    co
    #
    clog
    cfv
    #
    cA
    c1
    cmin
    co
    #
    cA
    cdiv
    co
    #
    clog
    cfv
    #
    caddc
    co
    #
    cA
    clog
    cfv
    #
    caddc
    co
    #
    cc
    ang180lem1.2
    @3
    @46
    @47
    @3
    @42
    @45
    @3
    @41
    @3
    @40
    @3
    c1
    cc
    wcel
    #
    @0
    @40
    cc
    wcel
    ax-1cn
    @0
    @1
    @2
    simp1
    #
    c1
    cA
    subcl
    sylancr
    #
    @3
    @40
    cc0
    wne
    c1
    cA
    wne
    @3
    cA
    c1
    @0
    @1
    @2
    simp3
    #
    necomd
    @3
    @40
    cc0
    c1
    cA
    @3
    @49
    @0
    @40
    cc0
    wceq
    c1
    cA
    wceq
    wb
    ax-1cn
    @50
    c1
    cA
    subeq0
    sylancr
    necon3bid
    mpbird
    #
    reccld
    @3
    @40
    @51
    @53
    recne0d
    logcld
    @3
    @44
    @3
    @43
    cA
    @3
    @0
    @49
    @43
    cc
    wcel
    @50
    ax-1cn
    cA
    c1
    subcl
    sylancl
    #
    @50
    @0
    @1
    @2
    simp2
    #
    divcld
    @3
    @43
    cA
    @54
    @50
    @3
    @43
    cc0
    wne
    @2
    @52
    @3
    @43
    cc0
    cA
    c1
    @3
    @0
    @49
    @43
    cc0
    wceq
    cA
    c1
    wceq
    wb
    @50
    ax-1cn
    cA
    c1
    subeq0
    sylancl
    necon3bid
    mpbird
    @55
    divne0d
    logcld
    addcld
    @0
    @1
    @47
    cc
    wcel
    @2
    cA
    logcl
    3adant3
    addcld
    syl5eqel
    #
    ci
    cc
    wcel
    #
    @3
    ax-icn
    a1i
    #
    ci
    cc0
    wne
    #
    @3
    ine0
    a1i
    #
    divcld
    #
    @14
    cc
    wcel
    #
    @3
    @17
    a1i
    #
    @14
    cc0
    wne
    #
    @3
    c2
    cpi
    2cn
    picn
    2ne0
    cpi
    pire
    pipos
    gt0ne0ii
    mulne0i
    #
    a1i
    #
    divcld
    #
    adantr
    halfcn
    @18
    @15
    subeq0
    sylancl
    mpbid
    @12
    @13
    @14
    @15
    @3
    @13
    cc
    wcel
    @10
    @61
    adantr
    @62
    @12
    @17
    a1i
    @39
    @12
    halfcn
    a1i
    @64
    @12
    @65
    a1i
    divmuld
    mpbid
    syl5reqr
    @12
    cT
    ci
    cpi
    @3
    cT
    cc
    wcel
    @10
    @56
    adantr
    @57
    @12
    ax-icn
    a1i
    cpi
    cc
    wcel
    @12
    picn
    a1i
    @59
    @12
    ine0
    a1i
    divmuld
    mpbid
    eqcomd
    olcd
    @3
    @11
    wa
    #
    @6
    @7
    @68
    @5
    @13
    ci
    cmul
    co
    #
    cT
    @68
    @5
    cpi
    cneg
    #
    ci
    cmul
    co
    #
    @69
    @71
    cpi
    ci
    cmul
    co
    #
    cneg
    @5
    cpi
    ci
    picn
    ax-icn
    mulneg1i
    @72
    @4
    cpi
    ci
    picn
    ax-icn
    mulcomi
    negeqi
    eqtri
    @68
    @70
    @13
    ci
    cmul
    @68
    @70
    @18
    @14
    cmul
    co
    #
    @13
    @68
    @70
    @15
    cneg
    #
    @14
    cmul
    co
    #
    @73
    @75
    @15
    @14
    cmul
    co
    #
    cneg
    @70
    @15
    @14
    halfcn
    @17
    mulneg1i
    @76
    cpi
    @15
    c2
    cmul
    co
    #
    cpi
    cmul
    co
    c1
    cpi
    cmul
    co
    @76
    cpi
    @77
    c1
    cpi
    cmul
    c1
    c2
    ax-1cn
    2cn
    2ne0
    divcan1i
    oveq1i
    @15
    c2
    cpi
    halfcn
    2cn
    picn
    mulassi
    cpi
    picn
    mulid2i
    3eqtr3i
    negeqi
    eqtri
    @68
    @74
    @18
    @14
    cmul
    @68
    @74
    @20
    @15
    caddc
    co
    #
    @18
    @68
    @74
    @9
    @15
    caddc
    co
    #
    @78
    c1
    @15
    cmin
    co
    #
    cneg
    @79
    @74
    c1
    @15
    ax-1cn
    halfcn
    negsubdii
    @80
    @15
    1mhlfehlf
    negeqi
    eqtr3i
    @68
    @9
    @20
    @15
    caddc
    @68
    @9
    cN
    @20
    @3
    @11
    simpr
    ang180lem1.3
    syl6eq
    oveq1d
    syl5eqr
    @3
    @78
    @18
    wceq
    #
    @11
    @3
    @38
    @39
    @81
    @67
    halfcn
    @18
    @15
    npcan
    sylancl
    adantr
    eqtrd
    oveq1d
    syl5eqr
    @3
    @73
    @13
    wceq
    @11
    @3
    @13
    @14
    @61
    @63
    @66
    divcan1d
    adantr
    eqtrd
    oveq1d
    syl5eqr
    @3
    @69
    cT
    wceq
    @11
    @3
    cT
    ci
    @56
    @58
    @60
    divcan1d
    adantr
    eqtr2d
    orcd
    @3
    @9
    cN
    cle
    wbr
    #
    @10
    @11
    wo
    #
    @3
    @82
    @9
    c1
    cmin
    co
    #
    cN
    clt
    wbr
    #
    @3
    @84
    @27
    cN
    clt
    @27
    c1
    c1
    caddc
    co
    #
    cneg
    #
    @84
    c2
    @86
    df-2
    negeqi
    @49
    @49
    @87
    @84
    wceq
    ax-1cn
    ax-1cn
    c1
    c1
    negdi2
    mp2an
    eqtri
    @3
    @28
    @29
    @30
    simpld
    syl5eqbrr
    @3
    @9
    cz
    wcel
    @31
    @82
    @85
    wb
    neg1z
    @33
    @9
    cN
    zlem1lt
    sylancr
    mpbird
    @3
    @9
    cr
    wcel
    @36
    @82
    @83
    wb
    neg1rr
    @37
    @9
    cN
    leloe
    sylancr
    mpbid
    mpjaodan
    cT
    @5
    @4
    cT
    @48
    cvv
    ang180lem1.2
    @46
    @47
    caddc
    ovex
    eqeltri
    elpr
    sylibr
end
