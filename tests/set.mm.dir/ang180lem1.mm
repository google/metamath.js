include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "w3a.mm"
include "cz.mm"
include "ci.mm"
include "cdiv.mm"
include "co.mm"
include "cr.mm"
include "cpi.mm"
include "cmul.mm"
include "cmin.mm"
include "c2.mm"
include "wa.mm"
include "wceq.mm"
include "picn.mm"
include "2re.mm"
include "pire.mm"
include "remulcli.mm"
include "recni.mm"
include "2pos.mm"
include "pipos.mm"
include "mulgt0ii.mm"
include "gt0ne0ii.mm"
include "pm3.2i.mm"
include "ax-icn.mm"
include "ine0.mm"
include "divcan5.mm"
include "mp3an.mm"
include "recdiv.mm"
include "mp4an.mm"
include "divcan4i.mm"
include "oveq2i.mm"
include "3eqtr2i.mm"
include "clog.mm"
include "cfv.mm"
include "caddc.mm"
include "ax-1cn.mm"
include "simp1.mm"
include "subcl.mm"
include "sylancr.mm"
include "simp3.mm"
include "necomd.mm"
include "wb.mm"
include "subeq0.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "reccld.mm"
include "recne0d.mm"
include "logcld.mm"
include "sylancl.mm"
include "simp2.mm"
include "divcld.mm"
include "divne0d.mm"
include "addcld.mm"
include "syl5eqel.mm"
include "mulcli.mm"
include "a1i.mm"
include "mulne0i.mm"
include "divsubdird.mm"
include "divdiv1.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "syl5eq.mm"
include "3eqtr4a.mm"
include "ce.mm"
include "efsub.mm"
include "cneg.mm"
include "efipi.mm"
include "fveq2i.mm"
include "efadd.mm"
include "syl2anc.mm"
include "eflog.mm"
include "oveq12d.mm"
include "mulcomd.mm"
include "div2negd.mm"
include "negsubdi2.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "neg1cn.mm"
include "dmdcand.mm"
include "3eqtrd.mm"
include "divcan1d.mm"
include "neg1ne0.mm"
include "dividi.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "efeq1.mm"
include "syl.mm"
include "mpbid.mm"
include "eqeltrrd.mm"
include "oveq1i.mm"
include "halfre.mm"
include "npcan.mm"
include "zred.mm"
include "readdcl.mm"
include "remulcl.mm"
include "jca.mm"

theorem ang180lem1
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
  assert |- ( ( A e. CC /\ A =/= 0 /\ A =/= 1 ) -> ( N e. ZZ /\ ( T / _i ) e. RR ) )

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
    cN
    cz
    wcel
    cT
    ci
    cdiv
    co
    #
    cr
    wcel
    @3
    cT
    ci
    cpi
    cmul
    co
    #
    cmin
    co
    #
    ci
    c2
    cpi
    cmul
    co
    #
    cmul
    co
    #
    cdiv
    co
    #
    cN
    cz
    @3
    cT
    @8
    cdiv
    co
    #
    @5
    @8
    cdiv
    co
    #
    cmin
    co
    @10
    c1
    c2
    cdiv
    co
    #
    cmin
    co
    #
    @9
    cN
    @11
    @12
    @10
    cmin
    @11
    cpi
    @7
    cdiv
    co
    #
    c1
    @7
    cpi
    cdiv
    co
    #
    cdiv
    co
    #
    @12
    cpi
    cc
    wcel
    #
    @7
    cc
    wcel
    #
    @7
    cc0
    wne
    #
    wa
    #
    ci
    cc
    wcel
    #
    ci
    cc0
    wne
    #
    wa
    #
    @11
    @14
    wceq
    picn
    @18
    @19
    @7
    c2
    cpi
    2re
    pire
    remulcli
    #
    recni
    #
    @7
    @24
    c2
    cpi
    2re
    pire
    2pos
    pipos
    mulgt0ii
    gt0ne0ii
    #
    pm3.2i
    #
    @21
    @22
    ax-icn
    ine0
    pm3.2i
    #
    cpi
    @7
    ci
    divcan5
    mp3an
    @18
    @19
    @17
    cpi
    cc0
    wne
    @16
    @14
    wceq
    @25
    @26
    picn
    cpi
    pire
    pipos
    gt0ne0ii
    #
    @7
    cpi
    recdiv
    mp4an
    @15
    c2
    c1
    cdiv
    c2
    cpi
    c2
    2re
    recni
    picn
    @29
    divcan4i
    oveq2i
    3eqtr2i
    oveq2i
    @3
    cT
    @5
    @8
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
    @36
    @37
    @3
    @32
    @35
    @3
    @31
    @3
    @30
    @3
    c1
    cc
    wcel
    #
    @0
    @30
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
    @30
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
    @30
    cc0
    c1
    cA
    @3
    @39
    @0
    @30
    cc0
    wceq
    c1
    cA
    wceq
    wb
    ax-1cn
    @40
    c1
    cA
    subeq0
    sylancr
    necon3bid
    mpbird
    #
    reccld
    #
    @3
    @30
    @41
    @43
    recne0d
    #
    logcld
    #
    @3
    @34
    @3
    @33
    cA
    @3
    @0
    @39
    @33
    cc
    wcel
    @40
    ax-1cn
    cA
    c1
    subcl
    sylancl
    #
    @40
    @0
    @1
    @2
    simp2
    #
    divcld
    #
    @3
    @33
    cA
    @47
    @40
    @3
    @33
    cc0
    wne
    @2
    @42
    @3
    @33
    cc0
    cA
    c1
    @3
    @0
    @39
    @33
    cc0
    wceq
    cA
    c1
    wceq
    wb
    @40
    ax-1cn
    cA
    c1
    subeq0
    sylancl
    necon3bid
    mpbird
    #
    @48
    divne0d
    #
    logcld
    #
    addcld
    #
    @3
    cA
    @40
    @48
    logcld
    #
    addcld
    syl5eqel
    #
    @5
    cc
    wcel
    #
    @3
    ci
    cpi
    ax-icn
    picn
    mulcli
    #
    a1i
    @8
    cc
    wcel
    @3
    ci
    @7
    ax-icn
    @25
    mulcli
    a1i
    @8
    cc0
    wne
    @3
    ci
    @7
    ax-icn
    @25
    ine0
    @26
    mulne0i
    a1i
    divsubdird
    @3
    cN
    @4
    @7
    cdiv
    co
    #
    @12
    cmin
    co
    #
    @13
    ang180lem1.3
    @3
    @58
    @10
    @12
    cmin
    @3
    cT
    cc
    wcel
    #
    @23
    @20
    @58
    @10
    wceq
    @55
    @23
    @3
    @28
    a1i
    @20
    @3
    @27
    a1i
    cT
    ci
    @7
    divdiv1
    syl3anc
    oveq1d
    syl5eq
    3eqtr4a
    @3
    @6
    ce
    cfv
    #
    c1
    wceq
    #
    @9
    cz
    wcel
    #
    @3
    @61
    cT
    ce
    cfv
    #
    @5
    ce
    cfv
    #
    cdiv
    co
    #
    c1
    @3
    @60
    @56
    @61
    @66
    wceq
    @55
    @57
    cT
    @5
    efsub
    sylancl
    @3
    @66
    @64
    c1
    cneg
    #
    cdiv
    co
    #
    c1
    @65
    @67
    @64
    cdiv
    efipi
    oveq2i
    @3
    @68
    @67
    @67
    cdiv
    co
    c1
    @3
    @64
    @67
    @67
    cdiv
    @3
    @64
    @38
    ce
    cfv
    #
    @67
    cT
    @38
    ce
    ang180lem1.2
    fveq2i
    @3
    @69
    @36
    ce
    cfv
    #
    @37
    ce
    cfv
    #
    cmul
    co
    #
    @67
    cA
    cdiv
    co
    #
    cA
    cmul
    co
    @67
    @3
    @36
    cc
    wcel
    @37
    cc
    wcel
    @69
    @72
    wceq
    @53
    @54
    @36
    @37
    efadd
    syl2anc
    @3
    @70
    @73
    @71
    cA
    cmul
    @3
    @70
    @32
    ce
    cfv
    #
    @35
    ce
    cfv
    #
    cmul
    co
    #
    @31
    @34
    cmul
    co
    #
    @73
    @3
    @32
    cc
    wcel
    @35
    cc
    wcel
    @70
    @76
    wceq
    @46
    @52
    @32
    @35
    efadd
    syl2anc
    @3
    @74
    @31
    @75
    @34
    cmul
    @3
    @31
    cc
    wcel
    @31
    cc0
    wne
    @74
    @31
    wceq
    @44
    @45
    @31
    eflog
    syl2anc
    @3
    @34
    cc
    wcel
    @34
    cc0
    wne
    @75
    @34
    wceq
    @49
    @51
    @34
    eflog
    syl2anc
    oveq12d
    @3
    @77
    @34
    @31
    cmul
    co
    @34
    @67
    @33
    cdiv
    co
    #
    cmul
    co
    @73
    @3
    @31
    @34
    @44
    @49
    mulcomd
    @3
    @31
    @78
    @34
    cmul
    @3
    @67
    @30
    cneg
    #
    cdiv
    co
    @31
    @78
    @3
    c1
    @30
    @39
    @3
    ax-1cn
    a1i
    @41
    @43
    div2negd
    @3
    @79
    @33
    @67
    cdiv
    @3
    @39
    @0
    @79
    @33
    wceq
    ax-1cn
    @40
    c1
    cA
    negsubdi2
    sylancr
    oveq2d
    eqtr3d
    oveq2d
    @3
    @67
    @33
    cA
    @67
    cc
    wcel
    @3
    neg1cn
    a1i
    #
    @47
    @40
    @50
    @48
    dmdcand
    3eqtrd
    3eqtrd
    @3
    @0
    @1
    @71
    cA
    wceq
    @40
    @48
    cA
    eflog
    syl2anc
    oveq12d
    @3
    @67
    cA
    @80
    @40
    @48
    divcan1d
    3eqtrd
    syl5eq
    oveq1d
    @67
    neg1cn
    neg1ne0
    dividi
    syl6eq
    syl5eq
    eqtrd
    @3
    @6
    cc
    wcel
    #
    @62
    @63
    wb
    @3
    @60
    @56
    @81
    @55
    @57
    cT
    @5
    subcl
    sylancl
    @6
    efeq1
    syl
    mpbid
    eqeltrrd
    #
    @3
    @58
    @7
    cmul
    co
    #
    @4
    cr
    @3
    @4
    @7
    @3
    cT
    ci
    @55
    @21
    @3
    ax-icn
    a1i
    @22
    @3
    ine0
    a1i
    divcld
    #
    @18
    @3
    @25
    a1i
    #
    @19
    @3
    @26
    a1i
    #
    divcan1d
    @3
    @58
    cr
    wcel
    @7
    cr
    wcel
    @83
    cr
    wcel
    @3
    cN
    @12
    caddc
    co
    #
    @58
    cr
    @3
    @87
    @59
    @12
    caddc
    co
    #
    @58
    cN
    @59
    @12
    caddc
    ang180lem1.3
    oveq1i
    @3
    @58
    cc
    wcel
    @12
    cc
    wcel
    @88
    @58
    wceq
    @3
    @4
    @7
    @84
    @85
    @86
    divcld
    @12
    halfre
    recni
    @58
    @12
    npcan
    sylancl
    syl5eq
    @3
    cN
    cr
    wcel
    @12
    cr
    wcel
    @87
    cr
    wcel
    @3
    cN
    @82
    zred
    halfre
    cN
    @12
    readdcl
    sylancl
    eqeltrrd
    @24
    @58
    @7
    remulcl
    sylancl
    eqeltrrd
    jca
end
