include "cv.mm"
include "cz.mm"
include "wcel.mm"
include "wss.mm"
include "cfn.mm"
include "w3a.mm"
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
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "cc0.mm"
include "cdif.mm"
include "wo.mm"
include "wb.mm"
include "0z.mm"
include "eqoreldif.mm"
include "ax-mp.mm"
include "simp2.mm"
include "snssi.mm"
include "3ad2ant1.mm"
include "unssd.mm"
include "mp1i.mm"
include "c0ex.mm"
include "snid.mm"
include "olci.mm"
include "elun.mm"
include "mpbir.mm"
include "lcmf0val.mm"
include "sylancl.mm"
include "adantr.mm"
include "sneq.mm"
include "adantl.mm"
include "uneq2d.mm"
include "fveq2d.mm"
include "oveq2.mm"
include "cn0.mm"
include "snfi.mm"
include "unfi.mm"
include "mpan2.mm"
include "3ad2ant3.mm"
include "lcmfcl.mm"
include "syl2anc.mm"
include "nn0zd.mm"
include "lcm0val.mm"
include "syl.mm"
include "sylan9eqr.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "com12.mm"
include "elun1.mm"
include "ad2antrr.mm"
include "oveq2d.mm"
include "eldifi.mm"
include "ad2antlr.mm"
include "eqtrd.mm"
include "simp3.mm"
include "lcmcom.mm"
include "syl2anr.mm"
include "snssd.mm"
include "orcd.mm"
include "sylibr.mm"
include "3eqtr4rd.mm"
include "a1d.mm"
include "impd.mm"
include "elsng.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "biimpri.mm"
include "olcd.mm"
include "syl2an2.mm"
include "syl5eleqr.mm"
include "wn.mm"
include "wnel.mm"
include "wne.mm"
include "ioran.mm"
include "df-nel.mm"
include "df-ne.mm"
include "anbi12i.mm"
include "bitr4i.mm"
include "eldif.mm"
include "velsn.mm"
include "bicomi.mm"
include "necon3abii.mm"
include "lcmfunsnlem2lem2.mm"
include "exp520.mm"
include "imp.mm"
include "syl5bir.mm"
include "com23.mm"
include "syl5bi.mm"
include "sylbi.mm"
include "ecase3.mm"
include "jaoi.mm"
include "ralrimi.mm"

theorem lcmfunsnlem2
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
  assert |- ( ( ( z e. ZZ /\ y C_ ZZ /\ y e. Fin ) /\ ( A. k e. ZZ ( A. m e. y m || k -> ( _lcm ` y ) || k ) /\ A. n e. ZZ ( _lcm ` ( y u. { n } ) ) = ( ( _lcm ` y ) lcm n ) ) ) -> A. n e. ZZ ( _lcm ` ( ( y u. { z } ) u. { n } ) ) = ( ( _lcm ` ( y u. { z } ) ) lcm n ) )

  proof
    vz
    cv
    #
    cz
    wcel
    #
    vy
    cv
    #
    cz
    wss
    #
    @2
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
    @2
    wral
    @2
    clcmf
    cfv
    #
    @6
    cdvds
    wbr
    wi
    vk
    cz
    wral
    #
    @2
    vn
    cv
    #
    csn
    #
    cun
    clcmf
    cfv
    @7
    @9
    clcm
    co
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
    @2
    @0
    csn
    #
    cun
    #
    @10
    cun
    #
    clcmf
    cfv
    #
    @16
    clcmf
    cfv
    #
    @9
    clcm
    co
    #
    wceq
    #
    vn
    cz
    @5
    @13
    vn
    @5
    vn
    nfv
    @8
    @12
    vn
    @8
    vn
    nfv
    @11
    vn
    cz
    nfra1
    nfan
    nfan
    @9
    cz
    wcel
    #
    @14
    @21
    @22
    @9
    cc0
    wceq
    #
    @9
    cz
    cc0
    csn
    #
    cdif
    wcel
    #
    wo
    #
    @14
    @21
    wi
    #
    cc0
    cz
    wcel
    #
    @22
    @26
    wb
    0z
    @9
    cc0
    cz
    eqoreldif
    ax-mp
    @23
    @27
    @25
    @14
    @23
    @21
    @5
    @23
    @21
    wi
    @13
    @5
    @23
    @21
    @5
    @23
    wa
    #
    @16
    @24
    cun
    #
    clcmf
    cfv
    #
    cc0
    @18
    @20
    @5
    @31
    cc0
    wceq
    #
    @23
    @5
    @30
    cz
    wss
    cc0
    @30
    wcel
    #
    @32
    @5
    @16
    @24
    cz
    @5
    @2
    @15
    cz
    @1
    @3
    @4
    simp2
    #
    @1
    @3
    @15
    cz
    wss
    #
    @4
    @0
    cz
    snssi
    3ad2ant1
    #
    unssd
    #
    @28
    @24
    cz
    wss
    @5
    0z
    cc0
    cz
    snssi
    mp1i
    unssd
    @33
    cc0
    @16
    wcel
    #
    cc0
    @24
    wcel
    #
    wo
    @39
    @38
    cc0
    c0ex
    snid
    #
    olci
    cc0
    @16
    @24
    elun
    mpbir
    @30
    lcmf0val
    sylancl
    adantr
    @29
    @17
    @30
    clcmf
    @29
    @10
    @24
    @16
    @23
    @10
    @24
    wceq
    @5
    @9
    cc0
    sneq
    adantl
    uneq2d
    fveq2d
    @23
    @5
    @20
    @19
    cc0
    clcm
    co
    #
    cc0
    @9
    cc0
    @19
    clcm
    oveq2
    @5
    @19
    cz
    wcel
    #
    @41
    cc0
    wceq
    @5
    @19
    @5
    @16
    cz
    wss
    #
    @16
    cfn
    wcel
    #
    @19
    cn0
    wcel
    #
    @37
    @4
    @1
    @44
    @3
    @4
    @15
    cfn
    wcel
    #
    @44
    @0
    snfi
    #
    @2
    @15
    unfi
    #
    mpan2
    3ad2ant3
    @16
    lcmfcl
    #
    syl2anc
    nn0zd
    @19
    lcm0val
    syl
    sylan9eqr
    3eqtr4d
    ex
    adantr
    com12
    cc0
    @2
    wcel
    #
    @0
    cc0
    wceq
    #
    @25
    @27
    wi
    #
    @50
    @25
    @27
    @50
    @25
    wa
    #
    @5
    @13
    @21
    @53
    @5
    @13
    @21
    wi
    #
    @53
    @5
    wa
    #
    @21
    @13
    @55
    @9
    @19
    clcm
    co
    #
    cc0
    @20
    @18
    @55
    @56
    @9
    cc0
    clcm
    co
    #
    cc0
    @55
    @19
    cc0
    @9
    clcm
    @55
    @43
    @38
    @19
    cc0
    wceq
    #
    @55
    @2
    @15
    cz
    @5
    @3
    @53
    @34
    adantl
    @5
    @35
    @53
    @36
    adantl
    unssd
    @50
    @38
    @25
    @5
    cc0
    @2
    @15
    elun1
    #
    ad2antrr
    @16
    lcmf0val
    #
    syl2anc
    oveq2d
    @25
    @57
    cc0
    wceq
    #
    @50
    @5
    @25
    @22
    @61
    @9
    cz
    @24
    eldifi
    #
    @9
    lcm0val
    #
    syl
    ad2antlr
    eqtrd
    @5
    @42
    @22
    @20
    @56
    wceq
    #
    @53
    @5
    @19
    @5
    @43
    @44
    @45
    @37
    @5
    @4
    @46
    @44
    @1
    @3
    @4
    simp3
    @47
    @48
    sylancl
    @49
    syl2anc
    nn0zd
    #
    @25
    @22
    @50
    @62
    adantl
    @19
    @9
    lcmcom
    #
    syl2anr
    @55
    @17
    cz
    wss
    #
    cc0
    @17
    wcel
    #
    @18
    cc0
    wceq
    #
    @55
    @16
    @10
    cz
    @5
    @43
    @53
    @37
    adantl
    @25
    @10
    cz
    wss
    #
    @50
    @5
    @25
    @9
    cz
    @62
    snssd
    #
    ad2antlr
    unssd
    @50
    @68
    @25
    @5
    @50
    @38
    cc0
    @10
    wcel
    #
    wo
    #
    @68
    @50
    @38
    @72
    @59
    orcd
    cc0
    @16
    @10
    elun
    #
    sylibr
    ad2antrr
    @17
    lcmf0val
    #
    syl2anc
    3eqtr4rd
    a1d
    ex
    impd
    ex
    @51
    @25
    @27
    @51
    @25
    wa
    #
    @5
    @13
    @21
    @76
    @5
    @54
    @76
    @5
    wa
    #
    @21
    @13
    @77
    @56
    cc0
    @20
    @18
    @77
    @56
    @57
    cc0
    @77
    @19
    cc0
    @9
    clcm
    @5
    @43
    @76
    @38
    @58
    @37
    @77
    @50
    cc0
    @15
    wcel
    #
    wo
    #
    @38
    @77
    @78
    @50
    @51
    @78
    @25
    @5
    @78
    @51
    @28
    @78
    @51
    wb
    0z
    @28
    @78
    cc0
    @0
    wceq
    @51
    cc0
    @0
    cz
    elsng
    cc0
    @0
    eqcom
    syl6bb
    ax-mp
    biimpri
    ad2antrr
    olcd
    cc0
    @2
    @15
    elun
    #
    sylibr
    @60
    syl2an2
    oveq2d
    @77
    @22
    @61
    @25
    @22
    @51
    @5
    @62
    ad2antlr
    #
    @63
    syl
    eqtrd
    @5
    @42
    @76
    @22
    @64
    @65
    @81
    @66
    syl2an2
    @77
    @67
    @68
    @69
    @77
    @16
    @10
    cz
    @5
    @43
    @76
    @37
    adantl
    @25
    @70
    @51
    @5
    @71
    ad2antlr
    unssd
    @77
    @73
    @68
    @77
    @38
    @72
    @77
    @79
    @38
    @77
    @78
    @50
    @51
    @78
    @25
    @5
    @51
    cc0
    @24
    @15
    @40
    @0
    cc0
    sneq
    syl5eleqr
    ad2antrr
    olcd
    @80
    sylibr
    orcd
    @74
    sylibr
    @75
    syl2anc
    3eqtr4rd
    a1d
    ex
    impd
    ex
    @50
    @51
    wo
    wn
    #
    cc0
    @2
    wnel
    #
    @0
    cc0
    wne
    #
    wa
    #
    @52
    @82
    @50
    wn
    #
    @51
    wn
    #
    wa
    @85
    @50
    @51
    ioran
    @83
    @86
    @84
    @87
    cc0
    @2
    df-nel
    @0
    cc0
    df-ne
    anbi12i
    bitr4i
    @25
    @22
    @9
    @24
    wcel
    #
    wn
    #
    wa
    @85
    @27
    @9
    cz
    @24
    eldif
    @85
    @22
    @89
    @27
    @85
    @89
    @22
    @27
    @89
    @9
    cc0
    wne
    #
    @85
    @22
    @27
    wi
    #
    @88
    @9
    cc0
    @88
    @23
    vn
    cc0
    velsn
    bicomi
    necon3abii
    @83
    @84
    @90
    @91
    wi
    @83
    @84
    @90
    @22
    @14
    @21
    vy
    vz
    vk
    vm
    vn
    lcmfunsnlem2lem2
    exp520
    imp
    syl5bir
    com23
    impd
    syl5bi
    sylbi
    ecase3
    jaoi
    sylbi
    com12
    ralrimi
end
