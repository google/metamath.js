include "cioo.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cr.mm"
include "clt.mm"
include "wbr.mm"
include "csup.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cle.mm"
include "wral.mm"
include "wrex.mm"
include "w3a.mm"
include "cicc.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "syl5ss.mm"
include "ivthlem1.mm"
include "simpld.mm"
include "ne0i.mm"
include "syl.mm"
include "simprd.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "3jca.mm"
include "suprcl.mm"
include "syl5eqel.mm"
include "wn.mm"
include "ivthlem2.mm"
include "wa.mm"
include "cmin.mm"
include "cabs.mm"
include "wi.mm"
include "crp.mm"
include "cc.mm"
include "ccncf.mm"
include "adantr.mm"
include "suprub.mm"
include "syl6breqr.mm"
include "wb.mm"
include "suprleub.mm"
include "mpbird.mm"
include "syl5eqbr.mm"
include "elicc2.mm"
include "mpbir3and.mm"
include "sseldd.mm"
include "ralrimiva.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "difrp.mm"
include "biimpa.mm"
include "cncfi.mm"
include "syl3anc.mm"
include "ssralv.mm"
include "ad2antrr.mm"
include "ltsubrp.mm"
include "sylancom.mm"
include "syl6breq.mm"
include "rpre.mm"
include "adantl.mm"
include "resubcld.mm"
include "suprlub.mm"
include "mpbid.mm"
include "sseli.mm"
include "ad2antrl.mm"
include "simplll.mm"
include "simprl.mm"
include "abssuble0d.mm"
include "simprr.mm"
include "ltsub23d.mm"
include "eqbrtrd.mm"
include "jca32.mm"
include "ex.mm"
include "reximdv2.mm"
include "mpd.mm"
include "r19.29.mm"
include "pm3.45.mm"
include "imp.mm"
include "caddc.mm"
include "ad2antll.mm"
include "absdifltd.mm"
include "recnd.mm"
include "nncand.mm"
include "breq1d.mm"
include "elrab2.mm"
include "simprbi.mm"
include "lenltd.mm"
include "pm2.21d.mm"
include "sylbid.mm"
include "adantrd.mm"
include "expr.mm"
include "com23.mm"
include "impd.mm"
include "syl5.mm"
include "rexlimdva.mm"
include "mpan2d.mm"
include "syld.mm"
include "pm2.01da.mm"
include "lttri3d.mm"
include "mpbir2and.mm"
include "breqtrrd.mm"
include "ltnrd.mm"
include "notbid.mm"
include "syl5ibcom.mm"
include "necon2ad.mm"
include "jctild.mm"
include "ltlend.mm"
include "sylibrd.mm"
include "breq2d.mm"
include "syl5ibrcom.mm"
include "cxr.mm"
include "rexrd.mm"
include "elioo2.mm"
include "jca.mm"

theorem ivthlem3
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cU: class U
  let cF: class F
  let vc: setvar c
  let vy: setvar y
  let vz: setvar z
  assume ivth.1: |- ( ph -> A e. RR )
  assume ivth.2: |- ( ph -> B e. RR )
  assume ivth.3: |- ( ph -> U e. RR )
  assume ivth.4: |- ( ph -> A < B )
  assume ivth.5: |- ( ph -> ( A [,] B ) C_ D )
  assume ivth.7: |- ( ph -> F e. ( D -cn-> CC ) )
  assume ivth.8: |- ( ( ph /\ x e. ( A [,] B ) ) -> ( F ` x ) e. RR )
  assume ivth.9: |- ( ph -> ( ( F ` A ) < U /\ U < ( F ` B ) ) )
  assume ivth.10: |- S = { x e. ( A [,] B ) | ( F ` x ) <_ U }
  assume ivth.11: |- C = sup ( S , RR , < )

  disjoint B x
  disjoint D x
  disjoint F x
  disjoint ph x
  disjoint A x
  disjoint C x
  disjoint S x
  disjoint U x
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint B c
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint D c
  disjoint D y
  disjoint D z
  disjoint F c
  disjoint F y
  disjoint F z
  disjoint c ph
  disjoint ph y
  disjoint ph z
  disjoint A c
  disjoint A y
  disjoint C y
  disjoint C z
  disjoint S y
  disjoint S z
  disjoint U c
  disjoint U y
  disjoint U z
  assert |- ( ph -> ( C e. ( A (,) B ) /\ ( F ` C ) = U ) )

  proof
    wph
    cC
    cA
    cB
    cioo
    co
    wcel
    #
    cC
    cF
    cfv
    #
    cU
    wceq
    #
    wph
    @0
    cC
    cr
    wcel
    #
    cA
    cC
    clt
    wbr
    #
    cC
    cB
    clt
    wbr
    #
    wph
    cC
    cS
    cr
    clt
    csup
    #
    cr
    ivth.11
    wph
    cS
    cr
    wss
    #
    cS
    c0
    wne
    #
    vz
    cv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vz
    cS
    wral
    #
    vx
    cr
    wrex
    #
    w3a
    #
    @6
    cr
    wcel
    wph
    @7
    @8
    @13
    wph
    cS
    cA
    cB
    cicc
    co
    #
    cr
    cS
    @10
    cF
    cfv
    #
    cU
    cle
    wbr
    #
    vx
    @15
    crab
    @15
    ivth.10
    @17
    vx
    @15
    ssrab2
    eqsstri
    #
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @15
    cr
    wss
    #
    ivth.1
    ivth.2
    cA
    cB
    iccssre
    syl2anc
    #
    syl5ss
    wph
    cA
    cS
    wcel
    #
    @8
    wph
    @23
    @9
    cB
    cle
    wbr
    #
    vz
    cS
    wral
    #
    wph
    vx
    vz
    cA
    cB
    cD
    cS
    cU
    cF
    ivth.1
    ivth.2
    ivth.3
    ivth.4
    ivth.5
    ivth.7
    ivth.8
    ivth.9
    ivth.10
    ivthlem1
    #
    simpld
    #
    cS
    cA
    ne0i
    syl
    wph
    @20
    @25
    @13
    ivth.2
    wph
    @23
    @25
    @26
    simprd
    #
    @12
    @25
    vx
    cB
    cr
    @10
    cB
    wceq
    @11
    @24
    vz
    cS
    @10
    cB
    @9
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    3jca
    #
    vx
    vz
    cS
    suprcl
    syl
    syl5eqel
    #
    wph
    cA
    cF
    cfv
    #
    @1
    clt
    wbr
    #
    @4
    wph
    @31
    cU
    @1
    clt
    wph
    @31
    cU
    clt
    wbr
    #
    cU
    cB
    cF
    cfv
    #
    clt
    wbr
    #
    ivth.9
    simpld
    wph
    @2
    @1
    cU
    clt
    wbr
    wn
    cU
    @1
    clt
    wbr
    #
    wn
    #
    wph
    vx
    cA
    cB
    cC
    cD
    cS
    cU
    cF
    ivth.1
    ivth.2
    ivth.3
    ivth.4
    ivth.5
    ivth.7
    ivth.8
    ivth.9
    ivth.10
    ivth.11
    ivthlem2
    wph
    @36
    wph
    @36
    wa
    #
    vy
    cv
    #
    cC
    cmin
    co
    cabs
    cfv
    #
    @9
    clt
    wbr
    #
    @39
    cF
    cfv
    #
    @1
    cmin
    co
    cabs
    cfv
    @1
    cU
    cmin
    co
    #
    clt
    wbr
    #
    wi
    #
    vy
    cD
    wral
    #
    vz
    crp
    wrex
    #
    @37
    @38
    cF
    cD
    cc
    ccncf
    co
    wcel
    #
    cC
    cD
    wcel
    #
    @43
    crp
    wcel
    #
    @47
    wph
    @48
    @36
    ivth.7
    adantr
    wph
    @49
    @36
    wph
    @15
    cD
    cC
    ivth.5
    wph
    cC
    @15
    wcel
    #
    @3
    cA
    cC
    cle
    wbr
    #
    cC
    cB
    cle
    wbr
    #
    @30
    wph
    cA
    @6
    cC
    cle
    wph
    @14
    @23
    cA
    @6
    cle
    wbr
    @29
    @27
    vx
    vz
    cS
    cA
    suprub
    syl2anc
    ivth.11
    syl6breqr
    #
    wph
    cC
    @6
    cB
    cle
    ivth.11
    wph
    @6
    cB
    cle
    wbr
    #
    @25
    @28
    wph
    @14
    @20
    @55
    @25
    wb
    @29
    ivth.2
    vx
    vz
    vz
    cS
    cB
    suprleub
    syl2anc
    mpbird
    syl5eqbr
    #
    wph
    @19
    @20
    @51
    @3
    @52
    @53
    w3a
    wb
    ivth.1
    ivth.2
    cA
    cB
    cC
    elicc2
    syl2anc
    mpbir3and
    #
    sseldd
    adantr
    wph
    @36
    @50
    wph
    cU
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    @36
    @50
    wb
    ivth.3
    wph
    @51
    @16
    cr
    wcel
    #
    vx
    @15
    wral
    #
    @59
    @57
    wph
    @60
    vx
    @15
    ivth.8
    ralrimiva
    #
    @60
    @59
    vx
    cC
    @15
    @10
    cC
    wceq
    @16
    @1
    cr
    @10
    cC
    cF
    fveq2
    eleq1d
    rspcv
    sylc
    #
    cU
    @1
    difrp
    syl2anc
    biimpa
    vz
    vy
    cD
    cc
    cC
    @43
    cF
    cncfi
    syl3anc
    @38
    @46
    @37
    vz
    crp
    @38
    @9
    crp
    wcel
    #
    wa
    #
    @46
    @45
    vy
    @15
    wral
    #
    @37
    wph
    @46
    @66
    wi
    #
    @36
    @64
    wph
    @15
    cD
    wss
    @67
    ivth.5
    @45
    vy
    @15
    cD
    ssralv
    syl
    ad2antrr
    @65
    @66
    @41
    @39
    cS
    wcel
    #
    wa
    #
    vy
    @15
    wrex
    #
    @37
    @65
    cC
    @9
    cmin
    co
    #
    @39
    clt
    wbr
    #
    vy
    cS
    wrex
    #
    @70
    @65
    @71
    @6
    clt
    wbr
    #
    @73
    @65
    @71
    cC
    @6
    clt
    @38
    @64
    @3
    @71
    cC
    clt
    wbr
    wph
    @3
    @36
    @64
    @30
    ad2antrr
    #
    cC
    @9
    ltsubrp
    sylancom
    ivth.11
    syl6breq
    @65
    @14
    @71
    cr
    wcel
    @74
    @73
    wb
    wph
    @14
    @36
    @64
    @29
    ad2antrr
    @65
    cC
    @9
    @75
    @64
    @9
    cr
    wcel
    #
    @38
    @9
    rpre
    adantl
    #
    resubcld
    vx
    vz
    vy
    cS
    @71
    suprlub
    syl2anc
    mpbid
    @65
    @72
    @69
    vy
    cS
    @15
    @65
    @68
    @72
    wa
    #
    @39
    @15
    wcel
    #
    @69
    wa
    @65
    @78
    wa
    #
    @79
    @41
    @68
    @68
    @79
    @65
    @72
    cS
    @15
    @39
    @18
    sseli
    #
    ad2antrl
    #
    @80
    @40
    cC
    @39
    cmin
    co
    @9
    clt
    @80
    @39
    cC
    @80
    @15
    cr
    @39
    @80
    wph
    @21
    wph
    @36
    @64
    @78
    simplll
    #
    @22
    syl
    @82
    sseldd
    #
    @80
    wph
    @3
    @83
    @30
    syl
    #
    @80
    @39
    @6
    cC
    cle
    @80
    @14
    @68
    @39
    @6
    cle
    wbr
    @80
    wph
    @14
    @83
    @29
    syl
    @65
    @68
    @72
    simprl
    #
    vx
    vz
    cS
    @39
    suprub
    syl2anc
    ivth.11
    syl6breqr
    abssuble0d
    @80
    cC
    @9
    @39
    @85
    @65
    @76
    @78
    @77
    adantr
    @84
    @65
    @68
    @72
    simprr
    ltsub23d
    eqbrtrd
    @86
    jca32
    ex
    reximdv2
    mpd
    @66
    @70
    wa
    @45
    @69
    wa
    #
    vy
    @15
    wrex
    @65
    @37
    @45
    @69
    vy
    @15
    r19.29
    @65
    @87
    @37
    vy
    @15
    @87
    @44
    @68
    wa
    #
    @65
    @79
    wa
    @37
    @45
    @69
    @88
    @41
    @44
    @68
    pm3.45
    imp
    @65
    @88
    @37
    wi
    @79
    @65
    @44
    @68
    @37
    @65
    @68
    @44
    @37
    @38
    @64
    @68
    @44
    @37
    wi
    @38
    @64
    @68
    wa
    #
    wa
    #
    @44
    @1
    @43
    cmin
    co
    #
    @42
    clt
    wbr
    #
    @42
    @1
    @43
    caddc
    co
    clt
    wbr
    #
    wa
    @37
    @90
    @42
    @1
    @43
    @90
    @79
    @61
    @42
    cr
    wcel
    #
    @68
    @79
    @38
    @64
    @81
    ad2antll
    wph
    @61
    @36
    @89
    @62
    ad2antrr
    @60
    @94
    vx
    @39
    @15
    @10
    @39
    wceq
    #
    @16
    @42
    cr
    @10
    @39
    cF
    fveq2
    #
    eleq1d
    rspcv
    sylc
    #
    wph
    @59
    @36
    @89
    @63
    ad2antrr
    #
    @90
    @1
    cU
    @98
    wph
    @58
    @36
    @89
    ivth.3
    ad2antrr
    #
    resubcld
    absdifltd
    @90
    @92
    @37
    @93
    @90
    @92
    cU
    @42
    clt
    wbr
    #
    @37
    @90
    @91
    cU
    @42
    clt
    @90
    @1
    cU
    @90
    @1
    @98
    recnd
    @90
    cU
    @99
    recnd
    nncand
    breq1d
    @90
    @100
    @37
    @90
    @42
    cU
    cle
    wbr
    #
    @100
    wn
    @68
    @101
    @38
    @64
    @68
    @79
    @101
    @17
    @101
    vx
    @39
    @15
    cS
    @95
    @16
    @42
    cU
    cle
    @96
    breq1d
    ivth.10
    elrab2
    simprbi
    ad2antll
    @90
    @42
    cU
    @97
    @99
    lenltd
    mpbid
    pm2.21d
    sylbid
    adantrd
    sylbid
    expr
    com23
    impd
    adantr
    syl5
    rexlimdva
    syl5
    mpan2d
    syld
    rexlimdva
    mpd
    pm2.01da
    wph
    @1
    cU
    @63
    ivth.3
    lttri3d
    mpbir2and
    #
    breqtrrd
    wph
    @32
    @52
    cC
    cA
    wne
    #
    wa
    @4
    wph
    @32
    @103
    @52
    wph
    @32
    cC
    cA
    wph
    @1
    @1
    clt
    wbr
    #
    wn
    #
    cC
    cA
    wceq
    #
    @32
    wn
    wph
    @1
    @63
    ltnrd
    #
    @106
    @104
    @32
    @106
    @1
    @31
    @1
    clt
    cC
    cA
    cF
    fveq2
    breq1d
    notbid
    syl5ibcom
    necon2ad
    @54
    jctild
    wph
    cA
    cC
    ivth.1
    @30
    ltlend
    sylibrd
    mpd
    wph
    @1
    @34
    clt
    wbr
    #
    @5
    wph
    @1
    cU
    @34
    clt
    @102
    wph
    @33
    @35
    ivth.9
    simprd
    eqbrtrd
    wph
    @108
    @53
    cB
    cC
    wne
    #
    wa
    @5
    wph
    @108
    @109
    @53
    wph
    @108
    cB
    cC
    wph
    @108
    wn
    cB
    cC
    wceq
    #
    @105
    @107
    @110
    @108
    @104
    @110
    @34
    @1
    @1
    clt
    cB
    cC
    cF
    fveq2
    breq2d
    notbid
    syl5ibrcom
    necon2ad
    @56
    jctild
    wph
    cC
    cB
    @30
    ivth.2
    ltlend
    sylibrd
    mpd
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    @0
    @3
    @4
    @5
    w3a
    wb
    wph
    cA
    ivth.1
    rexrd
    wph
    cB
    ivth.2
    rexrd
    cA
    cB
    cC
    elioo2
    syl2anc
    mpbir3and
    @102
    jca
end
