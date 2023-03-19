include "cc0.mm"
include "cv.mm"
include "wnel.mm"
include "wne.mm"
include "w3a.mm"
include "cz.mm"
include "wcel.mm"
include "wss.mm"
include "cfn.mm"
include "cdvds.mm"
include "wbr.mm"
include "wral.mm"
include "clcmf.mm"
include "cfv.mm"
include "wi.mm"
include "csn.mm"
include "cun.mm"
include "clcm.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cle.mm"
include "cn.mm"
include "wo.mm"
include "elun.mm"
include "wel.mm"
include "simp1.mm"
include "adantr.mm"
include "adantl.mm"
include "weq.mm"
include "sneq.mm"
include "uneq2d.mm"
include "fveq2d.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "syl.mm"
include "breq1.mm"
include "dvdslcmf.mm"
include "3adant1.mm"
include "impel.mm"
include "lcmfcl.mm"
include "nn0zd.mm"
include "cn0.mm"
include "lcmcl.mm"
include "sylan.mm"
include "jca.mm"
include "dvdslcm.mm"
include "simpld.mm"
include "ssel.mm"
include "3ad2ant2.mm"
include "impcom.mm"
include "syl2anc.mm"
include "dvdstr.mm"
include "syl3anc.mm"
include "mp2and.mm"
include "simpr.mm"
include "lcmass.mm"
include "breqtrrd.mm"
include "ex.mm"
include "elsni.mm"
include "simprd.mm"
include "syl5ibr.mm"
include "jaoi.mm"
include "imp.mm"
include "oveq1.mm"
include "breq2d.mm"
include "syl5ibrcom.mm"
include "syld.mm"
include "sylbi.mm"
include "simp2.mm"
include "snssi.mm"
include "3ad2ant1.mm"
include "unssd.mm"
include "simp3.mm"
include "snfi.mm"
include "unfi.mm"
include "sylancl.mm"
include "anim1i.mm"
include "expd.mm"
include "com13.mm"
include "ralrimiv.mm"
include "lcmfunsnlem2lem1.mm"
include "wb.mm"
include "wn.mm"
include "df-nel.mm"
include "biimpi.mm"
include "eqcomd.mm"
include "necon3ai.mm"
include "ioran.mm"
include "sylanbrc.mm"
include "sylnibr.mm"
include "sylibr.mm"
include "lcmfn0cl.mm"
include "nnne0d.mm"
include "neneqd.mm"
include "df-ne.mm"
include "3ad2ant3.mm"
include "lcmn0cl.mm"
include "mpan2.mm"
include "w3o.mm"
include "nnel.mm"
include "biimpri.mm"
include "3mix1d.mm"
include "nne.mm"
include "3mix2d.mm"
include "3mix3d.mm"
include "3ianor.mm"
include "con2i.mm"
include "3jca.mm"
include "lcmf.mm"
include "mpbird.mm"

theorem lcmfunsnlem2lem2
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vl: setvar l
  let vi: setvar i

  disjoint m y
  disjoint m z
  disjoint y z
  disjoint k n
  disjoint k y
  disjoint k z
  disjoint n y
  disjoint n z
  disjoint k m
  disjoint m n
  disjoint m x
  disjoint x y
  disjoint x z
  disjoint k x
  disjoint n x
  disjoint k l
  disjoint l m
  disjoint l y
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint i n
  disjoint i y
  disjoint i z
  disjoint l n
  disjoint l z
  assert |- ( ( ( 0 e/ y /\ z =/= 0 /\ n =/= 0 ) /\ ( n e. ZZ /\ ( ( z e. ZZ /\ y C_ ZZ /\ y e. Fin ) /\ ( A. k e. ZZ ( A. m e. y m || k -> ( _lcm ` y ) || k ) /\ A. n e. ZZ ( _lcm ` ( y u. { n } ) ) = ( ( _lcm ` y ) lcm n ) ) ) ) ) -> ( _lcm ` ( ( y u. { z } ) u. { n } ) ) = ( ( _lcm ` ( y u. { z } ) ) lcm n ) )

  proof
    cc0
    vy
    cv
    #
    wnel
    #
    vz
    cv
    #
    cc0
    wne
    #
    vn
    cv
    #
    cc0
    wne
    #
    w3a
    #
    @4
    cz
    wcel
    #
    @2
    cz
    wcel
    #
    @0
    cz
    wss
    #
    @0
    cfn
    wcel
    #
    w3a
    #
    vm
    cv
    vk
    cv
    #
    cdvds
    wbr
    vm
    @0
    wral
    @0
    clcmf
    cfv
    #
    @12
    cdvds
    wbr
    wi
    vk
    cz
    wral
    #
    @0
    @4
    csn
    #
    cun
    #
    clcmf
    cfv
    #
    @13
    @4
    clcm
    co
    #
    wceq
    #
    vn
    cz
    wral
    #
    wa
    #
    wa
    #
    wa
    #
    wa
    #
    @0
    @2
    csn
    #
    cun
    #
    clcmf
    cfv
    #
    @4
    clcm
    co
    #
    @26
    @15
    cun
    #
    clcmf
    cfv
    #
    @24
    @28
    @30
    wceq
    #
    vi
    cv
    #
    @28
    cdvds
    wbr
    #
    vi
    @29
    wral
    #
    @32
    @12
    cdvds
    wbr
    vi
    @29
    wral
    @28
    @12
    cle
    wbr
    wi
    vk
    cn
    wral
    #
    wa
    #
    @24
    @34
    @35
    @24
    @33
    vi
    @29
    @23
    @32
    @29
    wcel
    #
    @33
    wi
    #
    @6
    @22
    @7
    @38
    @21
    @11
    @7
    @38
    wi
    #
    @20
    @11
    @39
    wi
    @14
    @20
    @11
    @7
    @38
    @37
    @11
    @7
    wa
    #
    @20
    @33
    @37
    @32
    @26
    wcel
    #
    @32
    @15
    wcel
    #
    wo
    @40
    @20
    @33
    wi
    #
    wi
    #
    @32
    @26
    @15
    elun
    @41
    @44
    @42
    @41
    vi
    vy
    wel
    #
    @32
    @25
    wcel
    #
    wo
    #
    @44
    @32
    @0
    @25
    elun
    @47
    @40
    @43
    @47
    @40
    wa
    #
    @20
    @27
    @13
    @2
    clcm
    co
    #
    wceq
    #
    @33
    @48
    @8
    @20
    @50
    wi
    @40
    @8
    @47
    @11
    @8
    @7
    @8
    @9
    @10
    simp1
    #
    adantr
    #
    adantl
    @19
    @50
    vn
    @2
    cz
    vn
    vz
    weq
    #
    @17
    @27
    @18
    @49
    @53
    @16
    @26
    clcmf
    @53
    @15
    @25
    @0
    @4
    @2
    sneq
    uneq2d
    fveq2d
    @4
    @2
    @13
    clcm
    oveq2
    eqeq12d
    rspcv
    syl
    @48
    @33
    @50
    @32
    @49
    @4
    clcm
    co
    #
    cdvds
    wbr
    #
    @47
    @40
    @55
    @45
    @40
    @55
    wi
    #
    @46
    @45
    @40
    @55
    @45
    @40
    wa
    #
    @32
    @13
    @2
    @4
    clcm
    co
    #
    clcm
    co
    #
    @54
    cdvds
    @57
    @32
    @13
    cdvds
    wbr
    #
    @13
    @59
    cdvds
    wbr
    #
    @32
    @59
    cdvds
    wbr
    #
    @45
    @12
    @13
    cdvds
    wbr
    #
    vk
    @0
    wral
    #
    @60
    @40
    @63
    @60
    vk
    @32
    @0
    @12
    @32
    @13
    cdvds
    breq1
    rspcv
    @11
    @64
    @7
    @9
    @10
    @64
    @8
    vk
    @0
    dvdslcmf
    3adant1
    adantr
    impel
    @57
    @13
    cz
    wcel
    #
    @58
    cz
    wcel
    #
    wa
    #
    @61
    @40
    @67
    @45
    @40
    @65
    @66
    @11
    @65
    @7
    @9
    @10
    @65
    @8
    @9
    @10
    wa
    @13
    @0
    lcmfcl
    #
    nn0zd
    3adant1
    #
    adantr
    #
    @40
    @58
    @11
    @8
    @7
    @58
    cn0
    wcel
    @51
    @2
    @4
    lcmcl
    sylan
    nn0zd
    #
    jca
    adantl
    @67
    @61
    @58
    @59
    cdvds
    wbr
    @13
    @58
    dvdslcm
    simpld
    syl
    @57
    @32
    cz
    wcel
    #
    @65
    @59
    cz
    wcel
    @60
    @61
    wa
    @62
    wi
    @40
    @45
    @72
    @11
    @45
    @72
    wi
    #
    @7
    @9
    @8
    @73
    @10
    @0
    cz
    @32
    ssel
    3ad2ant2
    adantr
    impcom
    @40
    @65
    @45
    @70
    adantl
    #
    @57
    @59
    @57
    @65
    @66
    @59
    cn0
    wcel
    @74
    @40
    @66
    @45
    @71
    adantl
    @13
    @58
    lcmcl
    syl2anc
    nn0zd
    @32
    @13
    @59
    dvdstr
    syl3anc
    mp2and
    @57
    @65
    @8
    @7
    @54
    @59
    wceq
    @74
    @40
    @8
    @45
    @52
    adantl
    @40
    @7
    @45
    @11
    @7
    simpr
    adantl
    @4
    @2
    @13
    lcmass
    syl3anc
    breqtrrd
    ex
    @46
    vi
    vz
    weq
    #
    @56
    @32
    @2
    elsni
    @40
    @55
    @75
    @2
    @54
    cdvds
    wbr
    #
    @40
    @2
    @49
    cdvds
    wbr
    #
    @49
    @54
    cdvds
    wbr
    #
    @76
    @40
    @65
    @8
    wa
    #
    @77
    @11
    @79
    @7
    @11
    @65
    @8
    @69
    @51
    jca
    adantr
    @79
    @13
    @49
    cdvds
    wbr
    @77
    @13
    @2
    dvdslcm
    simprd
    syl
    @11
    @49
    cz
    wcel
    #
    @7
    @78
    @11
    @49
    @11
    @65
    @8
    @49
    cn0
    wcel
    @11
    @13
    @9
    @10
    @13
    cn0
    wcel
    @8
    @68
    3adant1
    nn0zd
    @51
    @13
    @2
    lcmcl
    syl2anc
    nn0zd
    #
    @80
    @7
    wa
    @78
    @4
    @54
    cdvds
    wbr
    @49
    @4
    dvdslcm
    simpld
    sylan
    @40
    @8
    @80
    @54
    cz
    wcel
    @77
    @78
    wa
    @76
    wi
    @52
    @11
    @80
    @7
    @81
    adantr
    @40
    @54
    @11
    @80
    @7
    @54
    cn0
    wcel
    @81
    @49
    @4
    lcmcl
    sylan
    nn0zd
    @2
    @49
    @54
    dvdstr
    syl3anc
    mp2and
    @32
    @2
    @54
    cdvds
    breq1
    syl5ibr
    syl
    jaoi
    imp
    @50
    @28
    @54
    @32
    cdvds
    @27
    @49
    @4
    clcm
    oveq1
    breq2d
    syl5ibrcom
    syld
    ex
    sylbi
    @42
    vi
    vn
    weq
    #
    @44
    @32
    @4
    elsni
    @82
    @40
    @20
    @33
    @40
    @20
    wa
    #
    @33
    @82
    @4
    @28
    cdvds
    wbr
    #
    @83
    @27
    @28
    cdvds
    wbr
    #
    @84
    @83
    @27
    cz
    wcel
    #
    @7
    wa
    #
    @85
    @84
    wa
    @40
    @87
    @20
    @11
    @86
    @7
    @11
    @27
    @11
    @26
    cz
    wss
    #
    @26
    cfn
    wcel
    #
    @27
    cn0
    wcel
    @11
    @0
    @25
    cz
    @8
    @9
    @10
    simp2
    @8
    @9
    @25
    cz
    wss
    @10
    @2
    cz
    snssi
    3ad2ant1
    unssd
    #
    @11
    @10
    @25
    cfn
    wcel
    #
    @89
    @8
    @9
    @10
    simp3
    @2
    snfi
    #
    @0
    @25
    unfi
    #
    sylancl
    #
    @26
    lcmfcl
    syl2anc
    nn0zd
    anim1i
    #
    adantr
    @27
    @4
    dvdslcm
    syl
    simprd
    @32
    @4
    @28
    cdvds
    breq1
    syl5ibr
    expd
    syl
    jaoi
    sylbi
    com13
    expd
    adantl
    impcom
    impcom
    adantl
    ralrimiv
    vy
    vz
    vi
    vk
    vm
    vn
    lcmfunsnlem2lem1
    jca
    @24
    @28
    cn
    wcel
    #
    @29
    cz
    wss
    #
    @29
    cfn
    wcel
    #
    cc0
    @29
    wnel
    #
    w3a
    #
    wa
    #
    @31
    @36
    wb
    @23
    @6
    @101
    @22
    @7
    @6
    @101
    wi
    #
    @11
    @7
    @102
    wi
    @21
    @11
    @7
    @102
    @40
    @6
    @101
    @40
    @6
    wa
    #
    @96
    @100
    @103
    @87
    @27
    cc0
    wceq
    #
    @4
    cc0
    wceq
    #
    wo
    wn
    #
    @96
    @40
    @87
    @6
    @95
    adantr
    @103
    @104
    wn
    @105
    wn
    #
    @106
    @103
    @27
    cc0
    @103
    @27
    @103
    @88
    @89
    cc0
    @26
    wnel
    #
    @27
    cn
    wcel
    @40
    @88
    @6
    @11
    @88
    @7
    @90
    adantr
    #
    adantr
    @40
    @89
    @6
    @11
    @89
    @7
    @94
    adantr
    adantr
    @6
    @108
    @40
    @6
    cc0
    @26
    wcel
    #
    wn
    @108
    @6
    cc0
    @0
    wcel
    #
    cc0
    @25
    wcel
    #
    wo
    #
    @110
    @6
    @111
    wn
    #
    @112
    wn
    #
    @113
    wn
    @1
    @3
    @114
    @5
    @1
    @114
    cc0
    @0
    df-nel
    biimpi
    3ad2ant1
    @3
    @1
    @115
    @5
    @112
    @2
    cc0
    @112
    cc0
    @2
    cc0
    @2
    elsni
    eqcomd
    #
    necon3ai
    3ad2ant2
    @111
    @112
    ioran
    sylanbrc
    cc0
    @0
    @25
    elun
    #
    sylnibr
    cc0
    @26
    df-nel
    sylibr
    adantl
    @26
    lcmfn0cl
    syl3anc
    nnne0d
    neneqd
    @6
    @107
    @40
    @5
    @1
    @107
    @3
    @5
    @107
    @4
    cc0
    df-ne
    biimpi
    3ad2ant3
    adantl
    @104
    @105
    ioran
    sylanbrc
    @27
    @4
    lcmn0cl
    syl2anc
    @103
    @97
    @98
    @99
    @40
    @97
    @6
    @40
    @26
    @15
    cz
    @109
    @7
    @15
    cz
    wss
    @11
    @4
    cz
    snssi
    adantl
    unssd
    adantr
    @40
    @98
    @6
    @11
    @98
    @7
    @10
    @8
    @98
    @9
    @10
    @89
    @15
    cfn
    wcel
    @98
    @10
    @91
    @89
    @92
    @93
    mpan2
    @4
    snfi
    @26
    @15
    unfi
    sylancl
    3ad2ant3
    adantr
    adantr
    @6
    @99
    @40
    @6
    cc0
    @29
    wcel
    #
    wn
    @99
    @118
    @6
    @118
    @1
    wn
    #
    @3
    wn
    #
    @5
    wn
    #
    w3o
    #
    @6
    wn
    @118
    @110
    cc0
    @15
    wcel
    #
    wo
    @122
    cc0
    @26
    @15
    elun
    @110
    @122
    @123
    @110
    @113
    @122
    @117
    @111
    @122
    @112
    @111
    @119
    @120
    @121
    @119
    @111
    cc0
    @0
    nnel
    biimpri
    3mix1d
    @112
    @120
    @119
    @121
    @112
    @2
    cc0
    wceq
    @120
    @116
    @2
    cc0
    nne
    sylibr
    3mix2d
    jaoi
    sylbi
    @123
    @121
    @119
    @120
    @123
    @105
    @121
    @123
    cc0
    @4
    cc0
    @4
    elsni
    eqcomd
    @4
    cc0
    nne
    sylibr
    3mix3d
    jaoi
    sylbi
    @1
    @3
    @5
    3ianor
    sylibr
    con2i
    cc0
    @29
    df-nel
    sylibr
    adantl
    3jca
    jca
    ex
    ex
    adantr
    impcom
    impcom
    vk
    vi
    @28
    @29
    lcmf
    syl
    mpbird
    eqcomd
end
