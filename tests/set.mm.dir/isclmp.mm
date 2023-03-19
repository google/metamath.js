include "cclm.mm"
include "wcel.mm"
include "clmod.mm"
include "ccnfld.mm"
include "cress.mm"
include "co.mm"
include "wceq.mm"
include "csubrg.mm"
include "cfv.mm"
include "w3a.mm"
include "cgrp.mm"
include "crg.mm"
include "wa.mm"
include "cv.mm"
include "cplusg.mm"
include "cmulr.mm"
include "cur.mm"
include "wral.mm"
include "c1.mm"
include "caddc.mm"
include "cmul.mm"
include "isclm.mm"
include "eqid.mm"
include "islmod.mm"
include "3anbi1i.mm"
include "3anass.mm"
include "df-3an.mm"
include "anbi1i.mm"
include "bitri.mm"
include "an32.mm"
include "3bitri.mm"
include "bicomi.mm"
include "anass.mm"
include "ancom.mm"
include "anbi12i.mm"
include "an4.mm"
include "wb.mm"
include "fveq2.mm"
include "subrg1.mm"
include "eqcomd.mm"
include "sylan9eq.mm"
include "cnfld1.mm"
include "syl6eqr.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "3adant1.mm"
include "ad2antrr.mm"
include "anbi1d.mm"
include "ressplusg.mm"
include "adantl.mm"
include "cnfldadd.mm"
include "a1i.mm"
include "adantr.mm"
include "3eqtr4rd.mm"
include "oveqd.mm"
include "ressmulr.mm"
include "3ad2ant3.mm"
include "cnfldmul.mm"
include "3ad2ant2.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "2ralbidva.mm"
include "ralcom.mm"
include "ralbii.mm"
include "2ralbii.mm"
include "syl6bb.mm"
include "subrgring.mm"
include "eleq1.mm"
include "mpbird.mm"
include "biantrurd.mm"
include "c0.mm"
include "wne.mm"
include "grpbn0.mm"
include "3ad2ant1.mm"
include "subrg1cl.mm"
include "ne0i.mm"
include "syl.mm"
include "ralbidv.mm"
include "r19.28zv.mm"
include "bitrd.mm"
include "anbi2i.mm"
include "weq.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "cbvralv.mm"
include "3anbi3i.mm"
include "3anan32.mm"
include "syl2anc.mm"
include "3bitr3d.mm"
include "pm5.32i.mm"

theorem isclmp
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let cK: class K
  let cV: class V
  let cW: class W
  let vr: setvar r
  assume isclmp.t: |- .x. = ( .s ` W )
  assume isclmp.a: |- .+ = ( +g ` W )
  assume isclmp.v: |- V = ( Base ` W )
  assume isclmp.s: |- S = ( Scalar ` W )
  assume isclmp.k: |- K = ( Base ` S )

  disjoint K x
  disjoint K y
  disjoint K z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint .x. x
  disjoint .x. y
  disjoint .x. z
  disjoint K r
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint S r
  disjoint V r
  disjoint W r
  disjoint .+ r
  disjoint .x. r
  assert |- ( W e. CMod <-> ( ( W e. Grp /\ S = ( CCfld |`s K ) /\ K e. ( SubRing ` CCfld ) ) /\ A. x e. V ( ( 1 .x. x ) = x /\ A. y e. K ( ( y .x. x ) e. V /\ A. z e. V ( y .x. ( x .+ z ) ) = ( ( y .x. x ) .+ ( y .x. z ) ) /\ A. z e. K ( ( ( z + y ) .x. x ) = ( ( z .x. x ) .+ ( y .x. x ) ) /\ ( ( z x. y ) .x. x ) = ( z .x. ( y .x. x ) ) ) ) ) ) )

  proof
    cW
    cclm
    wcel
    cW
    clmod
    wcel
    #
    cS
    ccnfld
    cK
    cress
    co
    #
    wceq
    #
    cK
    ccnfld
    csubrg
    cfv
    #
    wcel
    #
    w3a
    #
    cW
    cgrp
    wcel
    #
    cS
    crg
    wcel
    #
    wa
    #
    @2
    @4
    wa
    #
    wa
    #
    vy
    cv
    #
    vx
    cv
    #
    c.x
    co
    #
    cV
    wcel
    #
    @11
    @12
    vz
    cv
    #
    c.pl
    co
    c.x
    co
    @13
    @11
    @15
    c.x
    co
    c.pl
    co
    wceq
    #
    vr
    cv
    #
    @11
    cS
    cplusg
    cfv
    #
    co
    #
    @12
    c.x
    co
    #
    @17
    @12
    c.x
    co
    #
    @13
    c.pl
    co
    #
    wceq
    #
    w3a
    #
    @17
    @11
    cS
    cmulr
    cfv
    #
    co
    #
    @12
    c.x
    co
    #
    @17
    @13
    c.x
    co
    #
    wceq
    #
    cS
    cur
    cfv
    #
    @12
    c.x
    co
    #
    @12
    wceq
    #
    wa
    #
    wa
    #
    vx
    cV
    wral
    vz
    cV
    wral
    #
    vy
    cK
    wral
    vr
    cK
    wral
    #
    wa
    #
    @6
    @2
    @4
    w3a
    #
    c1
    @12
    c.x
    co
    #
    @12
    wceq
    #
    @14
    @16
    vz
    cV
    wral
    #
    @15
    @11
    caddc
    co
    #
    @12
    c.x
    co
    #
    @15
    @12
    c.x
    co
    #
    @13
    c.pl
    co
    #
    wceq
    #
    @15
    @11
    cmul
    co
    #
    @12
    c.x
    co
    #
    @15
    @13
    c.x
    co
    #
    wceq
    #
    wa
    #
    vz
    cK
    wral
    #
    w3a
    #
    vy
    cK
    wral
    wa
    #
    vx
    cV
    wral
    #
    wa
    #
    cS
    cK
    cW
    isclmp.s
    isclmp.k
    isclm
    @5
    @6
    @7
    @36
    w3a
    #
    @2
    @4
    w3a
    #
    @8
    @36
    wa
    #
    @9
    wa
    #
    @37
    @0
    @57
    @2
    @4
    vz
    vx
    c.pl
    @18
    c.x
    @25
    @30
    cS
    cK
    cV
    cW
    vy
    vr
    isclmp.v
    isclmp.a
    isclmp.t
    isclmp.s
    isclmp.k
    @18
    eqid
    @25
    eqid
    @30
    eqid
    islmod
    3anbi1i
    @58
    @57
    @9
    wa
    @60
    @57
    @2
    @4
    3anass
    @57
    @59
    @9
    @6
    @7
    @36
    df-3an
    anbi1i
    bitri
    @8
    @36
    @9
    an32
    3bitri
    @37
    @38
    @7
    wa
    #
    @36
    wa
    @38
    @7
    @36
    wa
    #
    wa
    @56
    @10
    @61
    @36
    @10
    @6
    @9
    wa
    #
    @7
    wa
    @61
    @6
    @7
    @9
    an32
    @63
    @38
    @7
    @38
    @63
    @6
    @2
    @4
    3anass
    bicomi
    anbi1i
    bitri
    anbi1i
    @38
    @7
    @36
    anass
    @38
    @62
    @55
    @38
    @36
    @40
    @14
    wa
    #
    @16
    wa
    #
    @17
    @11
    caddc
    co
    #
    @12
    c.x
    co
    #
    @22
    wceq
    #
    @17
    @11
    cmul
    co
    #
    @12
    c.x
    co
    #
    @28
    wceq
    #
    wa
    #
    wa
    #
    vr
    cK
    wral
    #
    vz
    cV
    wral
    #
    vy
    cK
    wral
    #
    vx
    cV
    wral
    #
    @62
    @55
    @38
    @36
    @73
    vx
    cV
    wral
    vz
    cV
    wral
    #
    vy
    cK
    wral
    #
    vr
    cK
    wral
    #
    @77
    @38
    @35
    @78
    vr
    vy
    cK
    cK
    @38
    @17
    cK
    wcel
    @11
    cK
    wcel
    wa
    #
    wa
    #
    @34
    @73
    vz
    vx
    cV
    cV
    @34
    @32
    @14
    wa
    #
    @16
    wa
    #
    @23
    @29
    wa
    #
    wa
    #
    @82
    @15
    cV
    wcel
    @12
    cV
    wcel
    wa
    #
    wa
    #
    @73
    @34
    @14
    @16
    wa
    #
    @23
    wa
    #
    @32
    @29
    wa
    #
    wa
    @89
    @32
    wa
    #
    @85
    wa
    @86
    @24
    @90
    @33
    @91
    @14
    @16
    @23
    df-3an
    @29
    @32
    ancom
    anbi12i
    @89
    @23
    @32
    @29
    an4
    @92
    @84
    @85
    @92
    @14
    @32
    wa
    #
    @16
    wa
    @84
    @14
    @16
    @32
    an32
    @93
    @83
    @16
    @14
    @32
    ancom
    anbi1i
    bitri
    anbi1i
    3bitri
    @88
    @84
    @65
    @85
    @72
    @88
    @83
    @64
    @16
    @88
    @32
    @40
    @14
    @38
    @32
    @40
    wb
    #
    @81
    @87
    @2
    @4
    @94
    @6
    @9
    @31
    @39
    @12
    @9
    @30
    c1
    @12
    c.x
    @9
    @30
    ccnfld
    cur
    cfv
    #
    c1
    @2
    @4
    @30
    @1
    cur
    cfv
    #
    @95
    cS
    @1
    cur
    fveq2
    @4
    @95
    @96
    cK
    ccnfld
    @1
    @95
    @1
    eqid
    #
    @95
    eqid
    #
    subrg1
    eqcomd
    sylan9eq
    cnfld1
    syl6eqr
    oveq1d
    eqeq1d
    3adant1
    ad2antrr
    anbi1d
    anbi1d
    @88
    @23
    @68
    @29
    @71
    @88
    @20
    @67
    @22
    @88
    @19
    @66
    @12
    c.x
    @38
    @19
    @66
    wceq
    @81
    @87
    @38
    @18
    caddc
    @17
    @11
    @2
    @4
    @18
    caddc
    wceq
    @6
    @9
    ccnfld
    cplusg
    cfv
    #
    @1
    cplusg
    cfv
    #
    caddc
    @18
    @4
    @99
    @100
    wceq
    @2
    cK
    @99
    ccnfld
    @1
    @3
    @97
    @99
    eqid
    ressplusg
    adantl
    caddc
    @99
    wceq
    @9
    cnfldadd
    a1i
    @2
    @18
    @100
    wceq
    @4
    cS
    @1
    cplusg
    fveq2
    adantr
    3eqtr4rd
    3adant1
    oveqd
    ad2antrr
    oveq1d
    eqeq1d
    @88
    @27
    @70
    @28
    @88
    @26
    @69
    @12
    c.x
    @38
    @26
    @69
    wceq
    @81
    @87
    @38
    @25
    cmul
    @17
    @11
    @38
    ccnfld
    cmulr
    cfv
    #
    @1
    cmulr
    cfv
    #
    cmul
    @25
    @4
    @6
    @101
    @102
    wceq
    @2
    cK
    ccnfld
    @1
    @101
    @3
    @97
    @101
    eqid
    ressmulr
    3ad2ant3
    cmul
    @101
    wceq
    @38
    cnfldmul
    a1i
    @2
    @6
    @25
    @102
    wceq
    @4
    cS
    @1
    cmulr
    fveq2
    3ad2ant2
    3eqtr4rd
    oveqd
    ad2antrr
    oveq1d
    eqeq1d
    anbi12d
    anbi12d
    syl5bb
    2ralbidva
    2ralbidva
    @80
    @73
    vz
    cV
    wral
    #
    vy
    cK
    wral
    #
    vr
    cK
    wral
    #
    vx
    cV
    wral
    #
    @103
    vr
    cK
    wral
    #
    vy
    cK
    wral
    #
    vx
    cV
    wral
    @77
    @80
    @104
    vx
    cV
    wral
    #
    vr
    cK
    wral
    @106
    @79
    @109
    vr
    cK
    @79
    @103
    vx
    cV
    wral
    #
    vy
    cK
    wral
    @109
    @78
    @110
    vy
    cK
    @73
    vz
    vx
    cV
    cV
    ralcom
    ralbii
    @103
    vy
    vx
    cK
    cV
    ralcom
    bitri
    ralbii
    @104
    vr
    vx
    cK
    cV
    ralcom
    bitri
    @105
    @108
    vx
    cV
    @103
    vr
    vy
    cK
    cK
    ralcom
    ralbii
    @107
    @75
    vx
    vy
    cV
    cK
    @73
    vr
    vz
    cK
    cV
    ralcom
    2ralbii
    3bitri
    syl6bb
    @38
    @7
    @36
    @38
    @7
    @1
    crg
    wcel
    #
    @4
    @6
    @111
    @2
    cK
    ccnfld
    @1
    @97
    subrgring
    3ad2ant3
    @2
    @6
    @7
    @111
    wb
    @4
    cS
    @1
    crg
    eleq1
    3ad2ant2
    mpbird
    biantrurd
    @38
    @76
    @54
    vx
    cV
    @38
    cV
    c0
    wne
    #
    cK
    c0
    wne
    #
    @76
    @54
    wb
    @6
    @2
    @112
    @4
    cV
    cW
    isclmp.v
    grpbn0
    3ad2ant1
    @4
    @6
    @113
    @2
    @4
    @95
    cK
    wcel
    @113
    cK
    ccnfld
    @95
    @98
    subrg1cl
    cK
    @95
    ne0i
    syl
    3ad2ant3
    @112
    @113
    wa
    #
    @76
    @40
    @53
    wa
    #
    vy
    cK
    wral
    #
    @54
    @114
    @75
    @115
    vy
    cK
    @114
    @75
    @40
    @14
    @72
    vr
    cK
    wral
    #
    wa
    #
    wa
    #
    @41
    wa
    #
    @115
    @114
    @75
    @119
    @16
    wa
    #
    vz
    cV
    wral
    #
    @120
    @114
    @74
    @121
    vz
    cV
    @114
    @74
    @16
    @64
    wa
    #
    @117
    wa
    #
    @121
    @114
    @74
    @123
    @72
    wa
    #
    vr
    cK
    wral
    #
    @124
    @114
    @73
    @125
    vr
    cK
    @73
    @125
    wb
    @114
    @65
    @123
    @72
    @64
    @16
    ancom
    anbi1i
    a1i
    ralbidv
    @113
    @126
    @124
    wb
    @112
    @123
    @72
    vr
    cK
    r19.28zv
    adantl
    bitrd
    @124
    @16
    @64
    @117
    wa
    #
    wa
    @16
    @119
    wa
    @121
    @16
    @64
    @117
    anass
    @127
    @119
    @16
    @40
    @14
    @117
    anass
    anbi2i
    @16
    @119
    ancom
    3bitri
    syl6bb
    ralbidv
    @112
    @122
    @120
    wb
    @113
    @119
    @16
    vz
    cV
    r19.28zv
    adantr
    bitrd
    @120
    @40
    @118
    @41
    wa
    #
    wa
    @115
    @40
    @118
    @41
    anass
    @128
    @53
    @40
    @53
    @128
    @53
    @14
    @41
    @117
    w3a
    @128
    @52
    @117
    @14
    @41
    @51
    @72
    vz
    vr
    cK
    vz
    vr
    weq
    #
    @46
    @68
    @50
    @71
    @129
    @43
    @67
    @45
    @22
    @129
    @42
    @66
    @12
    c.x
    @15
    @17
    @11
    caddc
    oveq1
    oveq1d
    @129
    @44
    @21
    @13
    c.pl
    @15
    @17
    @12
    c.x
    oveq1
    oveq1d
    eqeq12d
    @129
    @48
    @70
    @49
    @28
    @129
    @47
    @69
    @12
    c.x
    @15
    @17
    @11
    cmul
    oveq1
    oveq1d
    @15
    @17
    @13
    c.x
    oveq1
    eqeq12d
    anbi12d
    cbvralv
    3anbi3i
    @14
    @41
    @117
    3anan32
    bitri
    bicomi
    anbi2i
    bitri
    syl6bb
    ralbidv
    @113
    @116
    @54
    wb
    @112
    @40
    @53
    vy
    cK
    r19.28zv
    adantl
    bitrd
    syl2anc
    ralbidv
    3bitr3d
    pm5.32i
    3bitri
    3bitri
end
