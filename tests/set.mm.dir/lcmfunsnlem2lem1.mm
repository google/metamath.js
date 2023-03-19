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
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "wo.mm"
include "wn.mm"
include "simprr.mm"
include "cn0.mm"
include "simp2.mm"
include "snssi.mm"
include "3ad2ant1.mm"
include "unssd.mm"
include "simp3.mm"
include "snfi.mm"
include "unfi.mm"
include "sylancl.mm"
include "jca.mm"
include "lcmfcl.mm"
include "syl.mm"
include "nn0zd.mm"
include "adantl.mm"
include "adantr.mm"
include "simprl.mm"
include "3jca.mm"
include "df-nel.mm"
include "biimpi.mm"
include "elsni.mm"
include "eqcomd.mm"
include "necon3ai.mm"
include "anim12i.mm"
include "3adant3.mm"
include "ioran.mm"
include "elun.mm"
include "xchnxbir.mm"
include "bitri.mm"
include "sylibr.mm"
include "lcmfn0cl.mm"
include "nnne0d.mm"
include "neneqd.mm"
include "neneq.mm"
include "3ad2ant3.mm"
include "ad2antrr.mm"
include "exp43.mm"
include "adantrd.mm"
include "com23.mm"
include "imp32.mm"
include "imp.mm"
include "sneq.mm"
include "uneq2d.mm"
include "fveq2d.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "nnz.mm"
include "3adant1.mm"
include "simpll1.mm"
include "elun1.mm"
include "orcd.mm"
include "breq1.mm"
include "com12.mm"
include "ralrimiv.mm"
include "breq2.mm"
include "ralbidv.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "syl5bi.mm"
include "mpid.mm"
include "exp31.mm"
include "com24.mm"
include "impl.mm"
include "vsnid.mm"
include "olci.mm"
include "mpbir.mm"
include "orci.mm"
include "mp1i.mm"
include "lcmdvds.mm"
include "sylc.mm"
include "syl5ibr.mm"
include "expd.mm"
include "exp5j.mm"
include "syld.mm"
include "com34.mm"
include "lcmledvds.mm"
include "ralrimi.mm"

theorem lcmfunsnlem2lem1
  let vy: setvar y
  let vz: setvar z
  let vi: setvar i
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vl: setvar l

  disjoint m y
  disjoint m z
  disjoint y z
  disjoint k n
  disjoint k y
  disjoint k z
  disjoint n y
  disjoint n z
  disjoint k m
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i y
  disjoint i z
  disjoint m n
  disjoint m x
  disjoint x y
  disjoint x z
  disjoint k x
  disjoint n x
  disjoint k l
  disjoint l m
  disjoint l y
  disjoint i l
  disjoint l n
  disjoint l z
  assert |- ( ( ( 0 e/ y /\ z =/= 0 /\ n =/= 0 ) /\ ( n e. ZZ /\ ( ( z e. ZZ /\ y C_ ZZ /\ y e. Fin ) /\ ( A. k e. ZZ ( A. m e. y m || k -> ( _lcm ` y ) || k ) /\ A. n e. ZZ ( _lcm ` ( y u. { n } ) ) = ( ( _lcm ` y ) lcm n ) ) ) ) ) -> A. k e. NN ( A. i e. ( ( y u. { z } ) u. { n } ) i || k -> ( ( _lcm ` ( y u. { z } ) ) lcm n ) <_ k ) )

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
    #
    vk
    cv
    #
    cdvds
    wbr
    #
    vm
    @0
    wral
    #
    @0
    clcmf
    cfv
    #
    @13
    cdvds
    wbr
    #
    wi
    #
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
    @16
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
    vi
    cv
    #
    @13
    cdvds
    wbr
    #
    vi
    @0
    @2
    csn
    #
    cun
    #
    @20
    cun
    #
    wral
    #
    @33
    clcmf
    cfv
    #
    @4
    clcm
    co
    @13
    cle
    wbr
    #
    wi
    vk
    cn
    @6
    @28
    vk
    @6
    vk
    nfv
    @7
    @27
    vk
    @7
    vk
    nfv
    @11
    @26
    vk
    @11
    vk
    nfv
    @19
    @25
    vk
    @18
    vk
    cz
    nfra1
    @25
    vk
    nfv
    nfan
    nfan
    nfan
    nfan
    @29
    @13
    cn
    wcel
    #
    @35
    @37
    @29
    @38
    wa
    #
    @35
    wa
    #
    @38
    @36
    cz
    wcel
    #
    @7
    w3a
    #
    @36
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
    wa
    #
    @36
    @13
    cdvds
    wbr
    #
    @4
    @13
    cdvds
    wbr
    #
    wa
    @37
    @39
    @46
    @35
    @29
    @38
    @46
    @6
    @7
    @27
    @38
    @46
    wi
    #
    @6
    @27
    @7
    @49
    @6
    @11
    @7
    @49
    wi
    @26
    @6
    @11
    @7
    @38
    @46
    @6
    @11
    wa
    #
    @7
    @38
    wa
    #
    wa
    #
    @42
    @45
    @52
    @38
    @41
    @7
    @50
    @7
    @38
    simprr
    @50
    @41
    @51
    @11
    @41
    @6
    @11
    @36
    @11
    @33
    cz
    wss
    #
    @33
    cfn
    wcel
    #
    wa
    @36
    cn0
    wcel
    @11
    @53
    @54
    @11
    @0
    @32
    cz
    @8
    @9
    @10
    simp2
    @8
    @9
    @32
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
    @32
    cfn
    wcel
    @54
    @8
    @9
    @10
    simp3
    @2
    snfi
    @0
    @32
    unfi
    sylancl
    #
    jca
    @33
    lcmfcl
    syl
    nn0zd
    adantl
    adantr
    @50
    @7
    @38
    simprl
    3jca
    @52
    @43
    wn
    #
    @44
    wn
    #
    wa
    @45
    @52
    @57
    @58
    @52
    @36
    cc0
    @52
    @36
    @52
    @53
    @54
    cc0
    @33
    wnel
    #
    w3a
    #
    @36
    cn
    wcel
    @50
    @60
    @51
    @50
    @53
    @54
    @59
    @11
    @53
    @6
    @55
    adantl
    @11
    @54
    @6
    @56
    adantl
    @6
    @59
    @11
    @6
    cc0
    @0
    wcel
    #
    wn
    #
    cc0
    @32
    wcel
    #
    wn
    #
    wa
    #
    @59
    @1
    @3
    @65
    @5
    @1
    @62
    @3
    @64
    @1
    @62
    cc0
    @0
    df-nel
    biimpi
    @63
    @2
    cc0
    @63
    cc0
    @2
    cc0
    @2
    elsni
    eqcomd
    necon3ai
    anim12i
    3adant3
    @59
    cc0
    @33
    wcel
    #
    wn
    @65
    cc0
    @33
    df-nel
    @61
    @63
    wo
    @65
    @66
    @61
    @63
    ioran
    cc0
    @0
    @32
    elun
    xchnxbir
    bitri
    sylibr
    adantr
    3jca
    adantr
    @33
    lcmfn0cl
    syl
    nnne0d
    neneqd
    @6
    @58
    @11
    @51
    @5
    @1
    @58
    @3
    @4
    cc0
    neneq
    3ad2ant3
    ad2antrr
    jca
    @43
    @44
    ioran
    sylibr
    jca
    exp43
    adantrd
    com23
    imp32
    imp
    adantr
    @40
    @47
    @48
    @39
    @35
    @47
    @29
    @38
    @35
    @47
    wi
    #
    @6
    @28
    @38
    @67
    wi
    #
    @28
    @6
    @68
    @7
    @27
    @6
    @68
    wi
    #
    @27
    @7
    @69
    @27
    @7
    @38
    @6
    @67
    @27
    @7
    @38
    @6
    @67
    wi
    #
    @11
    @19
    @25
    @51
    @70
    wi
    #
    @11
    @25
    @19
    @71
    @11
    @25
    @36
    @16
    @2
    clcm
    co
    #
    wceq
    #
    @19
    @71
    wi
    #
    @8
    @9
    @25
    @73
    wi
    @10
    @24
    @73
    vn
    @2
    cz
    @4
    @2
    wceq
    #
    @22
    @36
    @23
    @72
    @75
    @21
    @33
    clcmf
    @75
    @20
    @32
    @0
    @4
    @2
    sneq
    uneq2d
    fveq2d
    @4
    @2
    @16
    clcm
    oveq2
    eqeq12d
    rspcv
    3ad2ant1
    @73
    @11
    @74
    @73
    @11
    @19
    @51
    @6
    @67
    @73
    @11
    @19
    wa
    #
    @51
    wa
    #
    @6
    wa
    #
    @35
    @47
    @78
    @35
    wa
    #
    @47
    @73
    @72
    @13
    cdvds
    wbr
    #
    @79
    @13
    cz
    wcel
    #
    @16
    cz
    wcel
    #
    @8
    w3a
    #
    @17
    @2
    @13
    cdvds
    wbr
    #
    wa
    @80
    @77
    @83
    @6
    @35
    @77
    @81
    @82
    @8
    @51
    @81
    @76
    @38
    @81
    @7
    @13
    nnz
    adantl
    #
    adantl
    @11
    @82
    @19
    @51
    @9
    @10
    @82
    @8
    @9
    @10
    wa
    @16
    @0
    lcmfcl
    nn0zd
    3adant1
    ad2antrr
    @8
    @9
    @10
    @19
    @51
    simpll1
    3jca
    ad2antrr
    @79
    @17
    @84
    @78
    @35
    @17
    @76
    @51
    @6
    @35
    @17
    wi
    #
    @11
    @19
    @51
    @6
    wa
    #
    @86
    wi
    @11
    @35
    @87
    @19
    @17
    @11
    @35
    @87
    @19
    @17
    wi
    @11
    @35
    wa
    #
    @87
    wa
    #
    @19
    @15
    @17
    @88
    @15
    @87
    @88
    @14
    vm
    @0
    @35
    @12
    @0
    wcel
    #
    @14
    wi
    @11
    @90
    @35
    @14
    @90
    @12
    @34
    wcel
    #
    @35
    @14
    wi
    @90
    @12
    @33
    wcel
    #
    @12
    @20
    wcel
    #
    wo
    @91
    @90
    @92
    @93
    @12
    @0
    @32
    elun1
    orcd
    @12
    @33
    @20
    elun
    sylibr
    @31
    @14
    vi
    @12
    @34
    @30
    @12
    @13
    cdvds
    breq1
    rspcv
    syl
    com12
    adantl
    ralrimiv
    adantr
    @19
    @12
    vl
    cv
    #
    cdvds
    wbr
    #
    vm
    @0
    wral
    #
    @16
    @94
    cdvds
    wbr
    #
    wi
    #
    vl
    cz
    wral
    #
    @89
    @18
    @18
    @98
    vk
    vl
    cz
    @13
    @94
    wceq
    #
    @15
    @96
    @17
    @97
    @100
    @14
    @95
    vm
    @0
    @13
    @94
    @12
    cdvds
    breq2
    ralbidv
    @13
    @94
    @16
    cdvds
    breq2
    imbi12d
    cbvralv
    @89
    @81
    @99
    @18
    wi
    @87
    @81
    @88
    @51
    @81
    @6
    @85
    adantr
    adantl
    @98
    @18
    vl
    @13
    cz
    @94
    @13
    wceq
    #
    @96
    @15
    @97
    @17
    @101
    @95
    @14
    vm
    @0
    @94
    @13
    @12
    cdvds
    breq2
    ralbidv
    @94
    @13
    @16
    cdvds
    breq2
    imbi12d
    rspcv
    syl
    syl5bi
    mpid
    exp31
    com24
    imp
    impl
    imp
    @78
    @35
    @84
    @2
    @34
    wcel
    #
    @35
    @84
    wi
    @78
    @102
    @2
    @33
    wcel
    #
    @2
    @20
    wcel
    #
    wo
    @103
    @104
    @103
    @2
    @0
    wcel
    #
    @2
    @32
    wcel
    #
    wo
    @106
    @105
    vz
    vsnid
    olci
    @2
    @0
    @32
    elun
    mpbir
    orci
    @2
    @33
    @20
    elun
    mpbir
    @31
    @84
    vi
    @2
    @34
    @30
    @2
    @13
    cdvds
    breq1
    rspcv
    mp1i
    imp
    jca
    @13
    @16
    @2
    lcmdvds
    sylc
    @36
    @72
    @13
    cdvds
    breq1
    syl5ibr
    expd
    exp5j
    com12
    syld
    com23
    imp32
    expd
    com34
    com12
    imp
    com12
    imp
    imp
    imp
    @39
    @35
    @48
    @4
    @34
    wcel
    #
    @35
    @48
    wi
    @39
    @107
    @4
    @33
    wcel
    #
    @4
    @20
    wcel
    #
    wo
    @109
    @108
    vn
    vsnid
    olci
    @4
    @33
    @20
    elun
    mpbir
    @31
    @48
    vi
    @4
    @34
    @30
    @4
    @13
    cdvds
    breq1
    rspcv
    mp1i
    imp
    jca
    @13
    @36
    @4
    lcmledvds
    sylc
    exp31
    ralrimi
end
