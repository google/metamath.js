include "crp.mm"
include "wcel.mm"
include "cc.mm"
include "w3a.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "cv.mm"
include "cmin.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cmul.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "rphalfcl.mm"
include "3ad2ant1.mm"
include "cr.mm"
include "abscl.mm"
include "3ad2ant3.mm"
include "3ad2ant2.mm"
include "1re.mm"
include "readdcl.mm"
include "sylancl.mm"
include "cc0.mm"
include "cle.mm"
include "absge0.mm"
include "0lt1.mm"
include "addgegt0.mm"
include "an4s.mm"
include "mpanr12.mm"
include "syl2anc.mm"
include "elrpd.mm"
include "rpdivcld.mm"
include "rpred.mm"
include "readdcld.mm"
include "elrp.mm"
include "sylan2b.mm"
include "syl21anc.mm"
include "simprl.mm"
include "simpl2.mm"
include "subcld.mm"
include "abscld.mm"
include "adantr.mm"
include "ltmuldivd.mm"
include "simprr.mm"
include "simpl3.mm"
include "abs2difd.mm"
include "resubcld.mm"
include "lelttr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "ltsubadd2d.mm"
include "sylibd.mm"
include "ltle.mm"
include "syld.mm"
include "absge0d.mm"
include "lemul2a.mm"
include "ex.mm"
include "syl112anc.mm"
include "remulcld.mm"
include "expd.mm"
include "3syld.mm"
include "com23.mm"
include "sylbird.mm"
include "impd.mm"
include "absmuld.mm"
include "subdird.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "breq1d.mm"
include "ltmuldiv2d.mm"
include "subdid.mm"
include "lep1d.mm"
include "jca.mm"
include "lemul1a.mm"
include "syl3an3.mm"
include "mpd.mm"
include "eqbrtrd.mm"
include "mulcld.mm"
include "adantld.mm"
include "jcad.mm"
include "mulcl.mm"
include "adantl.mm"
include "simpl1.mm"
include "abs3lem.mm"
include "syl22anc.mm"
include "ralrimivva.mm"
include "wceq.mm"
include "breq2.mm"
include "anbi1d.mm"
include "imbi1d.mm"
include "2ralbidv.mm"
include "anbi2d.mm"
include "rspc2ev.mm"

theorem mulcn2
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let cT: class T

  disjoint u v
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B u
  disjoint B v
  disjoint B y
  disjoint B z
  disjoint C u
  disjoint C v
  disjoint C y
  disjoint C z
  disjoint u w
  disjoint v w
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B w
  disjoint C w
  disjoint T y
  disjoint T z
  assert |- ( ( A e. RR+ /\ B e. CC /\ C e. CC ) -> E. y e. RR+ E. z e. RR+ A. u e. CC A. v e. CC ( ( ( abs ` ( u - B ) ) < y /\ ( abs ` ( v - C ) ) < z ) -> ( abs ` ( ( u x. v ) - ( B x. C ) ) ) < A ) )

  proof
    cA
    crp
    wcel
    #
    cB
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    w3a
    #
    cA
    c2
    cdiv
    co
    #
    cC
    cabs
    cfv
    #
    @4
    cB
    cabs
    cfv
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
    cdiv
    co
    #
    crp
    wcel
    @8
    crp
    wcel
    #
    vu
    cv
    #
    cB
    cmin
    co
    #
    cabs
    cfv
    #
    @10
    clt
    wbr
    #
    vv
    cv
    #
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    @8
    clt
    wbr
    #
    wa
    #
    @12
    @16
    cmul
    co
    #
    cB
    cC
    cmul
    co
    #
    cmin
    co
    cabs
    cfv
    cA
    clt
    wbr
    #
    wi
    #
    vv
    cc
    wral
    vu
    cc
    wral
    #
    @14
    vy
    cv
    #
    clt
    wbr
    #
    @18
    vz
    cv
    #
    clt
    wbr
    #
    wa
    #
    @23
    wi
    #
    vv
    cc
    wral
    vu
    cc
    wral
    #
    vz
    crp
    wrex
    vy
    crp
    wrex
    @3
    @4
    @9
    @0
    @1
    @4
    crp
    wcel
    #
    @2
    cA
    rphalfcl
    3ad2ant1
    #
    @3
    @9
    @3
    @5
    @8
    @2
    @0
    @5
    cr
    wcel
    #
    @1
    cC
    abscl
    3ad2ant3
    #
    @3
    @8
    @3
    @4
    @7
    @34
    @3
    @7
    @3
    @6
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
    @1
    @0
    @37
    @2
    cB
    abscl
    #
    3ad2ant2
    1re
    @6
    c1
    readdcl
    sylancl
    #
    @1
    @0
    cc0
    @7
    clt
    wbr
    #
    @2
    @1
    @37
    cc0
    @6
    cle
    wbr
    #
    @42
    @40
    cB
    absge0
    @37
    @43
    wa
    @38
    cc0
    c1
    clt
    wbr
    #
    @42
    1re
    0lt1
    @37
    @38
    @43
    @44
    @42
    @6
    c1
    addgegt0
    an4s
    mpanr12
    syl2anc
    3ad2ant2
    elrpd
    #
    rpdivcld
    #
    rpred
    #
    readdcld
    #
    @3
    @35
    cc0
    @5
    cle
    wbr
    #
    @11
    cc0
    @9
    clt
    wbr
    #
    @36
    @2
    @0
    @49
    @1
    cC
    absge0
    3ad2ant3
    @46
    @11
    @35
    @49
    wa
    @8
    cr
    wcel
    #
    cc0
    @8
    clt
    wbr
    #
    wa
    @50
    @8
    elrp
    @35
    @51
    @49
    @52
    @50
    @5
    @8
    addgegt0
    an4s
    sylan2b
    syl21anc
    elrpd
    #
    rpdivcld
    @46
    @3
    @24
    vu
    vv
    cc
    cc
    @3
    @12
    cc
    wcel
    #
    @16
    cc
    wcel
    #
    wa
    #
    wa
    #
    @20
    @21
    cB
    @16
    cmul
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @4
    clt
    wbr
    #
    @58
    @22
    cmin
    co
    #
    cabs
    cfv
    #
    @4
    clt
    wbr
    #
    wa
    #
    @23
    @57
    @20
    @61
    @64
    @57
    @20
    @14
    @16
    cabs
    cfv
    #
    cmul
    co
    #
    @4
    clt
    wbr
    #
    @61
    @57
    @15
    @19
    @68
    @57
    @15
    @14
    @9
    cmul
    co
    #
    @4
    clt
    wbr
    #
    @19
    @68
    wi
    @57
    @14
    @4
    @9
    @57
    @13
    @57
    @12
    cB
    @3
    @54
    @55
    simprl
    #
    @0
    @1
    @2
    @56
    simpl2
    #
    subcld
    #
    abscld
    #
    @57
    @4
    @3
    @33
    @56
    @34
    adantr
    rpred
    #
    @3
    @9
    crp
    wcel
    @56
    @53
    adantr
    ltmuldivd
    @57
    @19
    @70
    @68
    @57
    @19
    @66
    @9
    cle
    wbr
    #
    @67
    @69
    cle
    wbr
    #
    @70
    @68
    wi
    @57
    @19
    @66
    @9
    clt
    wbr
    #
    @76
    @57
    @19
    @66
    @5
    cmin
    co
    #
    @8
    clt
    wbr
    #
    @78
    @57
    @79
    @18
    cle
    wbr
    #
    @19
    @80
    @57
    @16
    cC
    @3
    @54
    @55
    simprr
    #
    @0
    @1
    @2
    @56
    simpl3
    #
    abs2difd
    @57
    @79
    cr
    wcel
    @18
    cr
    wcel
    #
    @51
    @81
    @19
    wa
    @80
    wi
    @57
    @66
    @5
    @57
    @16
    @82
    abscld
    #
    @3
    @35
    @56
    @36
    adantr
    #
    resubcld
    @57
    @17
    @57
    @16
    cC
    @82
    @83
    subcld
    #
    abscld
    #
    @3
    @51
    @56
    @47
    adantr
    #
    @79
    @18
    @8
    lelttr
    syl3anc
    mpand
    @57
    @66
    @5
    @8
    @85
    @86
    @89
    ltsubadd2d
    sylibd
    @57
    @66
    cr
    wcel
    #
    @9
    cr
    wcel
    #
    @78
    @76
    wi
    @85
    @3
    @91
    @56
    @48
    adantr
    #
    @66
    @9
    ltle
    syl2anc
    syld
    @57
    @90
    @91
    @14
    cr
    wcel
    #
    cc0
    @14
    cle
    wbr
    #
    @76
    @77
    wi
    @85
    @92
    @74
    @57
    @13
    @73
    absge0d
    @90
    @91
    @93
    @94
    wa
    w3a
    @76
    @77
    @66
    @9
    @14
    lemul2a
    ex
    syl112anc
    @57
    @77
    @70
    @68
    @57
    @67
    cr
    wcel
    @69
    cr
    wcel
    @4
    cr
    wcel
    #
    @77
    @70
    wa
    @68
    wi
    @57
    @14
    @66
    @74
    @85
    remulcld
    @57
    @14
    @9
    @74
    @92
    remulcld
    @75
    @67
    @69
    @4
    lelttr
    syl3anc
    expd
    3syld
    com23
    sylbird
    impd
    @57
    @67
    @60
    @4
    clt
    @57
    @13
    @16
    cmul
    co
    #
    cabs
    cfv
    @67
    @60
    @57
    @13
    @16
    @73
    @82
    absmuld
    @57
    @96
    @59
    cabs
    @57
    @12
    cB
    @16
    @71
    @72
    @82
    subdird
    fveq2d
    eqtr3d
    breq1d
    sylibd
    @57
    @19
    @64
    @15
    @57
    @19
    @7
    @18
    cmul
    co
    #
    @4
    clt
    wbr
    #
    @64
    @57
    @18
    @4
    @7
    @88
    @75
    @3
    @7
    crp
    wcel
    @56
    @45
    adantr
    ltmuldiv2d
    @57
    @63
    @97
    cle
    wbr
    #
    @98
    @64
    @57
    @63
    @6
    @18
    cmul
    co
    #
    @97
    cle
    @57
    cB
    @17
    cmul
    co
    #
    cabs
    cfv
    @63
    @100
    @57
    @101
    @62
    cabs
    @57
    cB
    @16
    cC
    @72
    @82
    @83
    subdid
    fveq2d
    @57
    cB
    @17
    @72
    @87
    absmuld
    eqtr3d
    @57
    @6
    @7
    cle
    wbr
    #
    @100
    @97
    cle
    wbr
    #
    @57
    @6
    @57
    cB
    @72
    abscld
    #
    lep1d
    @57
    @37
    @39
    @17
    cc
    wcel
    #
    @102
    @103
    wi
    #
    @104
    @3
    @39
    @56
    @41
    adantr
    #
    @87
    @105
    @37
    @39
    @84
    cc0
    @18
    cle
    wbr
    #
    wa
    #
    @106
    @105
    @84
    @108
    @17
    abscl
    @17
    absge0
    jca
    @37
    @39
    @109
    w3a
    @102
    @103
    @6
    @7
    @18
    lemul1a
    ex
    syl3an3
    syl3anc
    mpd
    eqbrtrd
    @57
    @63
    cr
    wcel
    @97
    cr
    wcel
    @95
    @99
    @98
    wa
    @64
    wi
    @57
    @62
    @57
    @58
    @22
    @57
    cB
    @16
    @72
    @82
    mulcld
    #
    @57
    cB
    cC
    @72
    @83
    mulcld
    #
    subcld
    abscld
    @57
    @7
    @18
    @107
    @88
    remulcld
    @75
    @63
    @97
    @4
    lelttr
    syl3anc
    mpand
    sylbird
    adantld
    jcad
    @57
    @21
    cc
    wcel
    #
    @22
    cc
    wcel
    @58
    cc
    wcel
    cA
    cr
    wcel
    @65
    @23
    wi
    @56
    @112
    @3
    @12
    @16
    mulcl
    adantl
    @111
    @110
    @57
    cA
    @0
    @1
    @2
    @56
    simpl1
    rpred
    @21
    @22
    @58
    cA
    abs3lem
    syl22anc
    syld
    ralrimivva
    @32
    @25
    @15
    @29
    wa
    #
    @23
    wi
    #
    vv
    cc
    wral
    vu
    cc
    wral
    vy
    vz
    @10
    @8
    crp
    crp
    @26
    @10
    wceq
    #
    @31
    @114
    vu
    vv
    cc
    cc
    @115
    @30
    @113
    @23
    @115
    @27
    @15
    @29
    @26
    @10
    @14
    clt
    breq2
    anbi1d
    imbi1d
    2ralbidv
    @28
    @8
    wceq
    #
    @114
    @24
    vu
    vv
    cc
    cc
    @116
    @113
    @20
    @23
    @116
    @29
    @19
    @15
    @28
    @8
    @18
    clt
    breq2
    anbi2d
    imbi1d
    2ralbidv
    rspc2ev
    syl3anc
end
