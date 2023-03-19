include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "wn.mm"
include "cc.mm"
include "ccncf.mm"
include "wcel.mm"
include "adantr.mm"
include "cicc.mm"
include "cr.mm"
include "cle.mm"
include "csup.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
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
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "3jca.mm"
include "suprcl.mm"
include "syl5eqel.mm"
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
include "c2.mm"
include "cdiv.mm"
include "caddc.mm"
include "cif.mm"
include "rphalfcl.mm"
include "adantl.mm"
include "rpred.mm"
include "readdcld.mm"
include "ifcld.mm"
include "cxr.mm"
include "rexrd.mm"
include "ltled.mm"
include "ubicc2.mm"
include "lttr.mm"
include "mpan2d.mm"
include "imp.mm"
include "ltnrd.mm"
include "breq2d.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "necon2ad.mm"
include "jctild.mm"
include "ltlend.mm"
include "sylibrd.mm"
include "mpd.mm"
include "ltaddrpd.mm"
include "ifboth.mm"
include "letrd.mm"
include "min1.mm"
include "abssubge0d.mm"
include "rpre.mm"
include "min2.mm"
include "rphalflt.mm"
include "ltadd2dd.mm"
include "lelttrd.mm"
include "ltsubadd2d.mm"
include "eqbrtrd.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "syl12anc.mm"
include "r19.29.mm"
include "pm3.45.mm"
include "simprr.mm"
include "simprl.mm"
include "simplll.mm"
include "resubcld.mm"
include "absdifltd.mm"
include "ltle.mm"
include "recnd.mm"
include "pncan3d.mm"
include "elrab2.mm"
include "baib.mm"
include "ad2antrl.mm"
include "3imtr4d.mm"
include "ex.mm"
include "3syl.mm"
include "lenltd.mm"
include "sylibd.mm"
include "syld.mm"
include "adantld.mm"
include "sylbid.mm"
include "mt2d.mm"
include "pm2.21d.mm"
include "expr.mm"
include "com23.mm"
include "impd.mm"
include "syl5.mm"
include "rexlimdva.mm"
include "pm2.01da.mm"

theorem ivthlem2
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
  assert |- ( ph -> -. ( F ` C ) < U )

  proof
    wph
    cC
    cF
    cfv
    #
    cU
    clt
    wbr
    #
    wph
    @1
    wa
    #
    vy
    cv
    #
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    vz
    cv
    #
    clt
    wbr
    #
    @3
    cF
    cfv
    #
    @0
    cmin
    co
    cabs
    cfv
    cU
    @0
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
    @1
    wn
    #
    @2
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
    @9
    crp
    wcel
    #
    @13
    wph
    @15
    @1
    ivth.7
    adantr
    wph
    @16
    @1
    wph
    cA
    cB
    cicc
    co
    #
    cD
    cC
    ivth.5
    wph
    cC
    @18
    wcel
    #
    cC
    cr
    wcel
    #
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
    @6
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
    @23
    cr
    wcel
    wph
    @24
    @25
    @29
    wph
    cS
    @18
    cr
    cS
    @26
    cF
    cfv
    #
    cU
    cle
    wbr
    #
    vx
    @18
    crab
    @18
    ivth.10
    @32
    vx
    @18
    ssrab2
    eqsstri
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @18
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
    @25
    wph
    @37
    @6
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
    @34
    @39
    @29
    ivth.2
    wph
    @37
    @39
    @40
    simprd
    #
    @28
    @39
    vx
    cB
    cr
    @26
    cB
    wceq
    #
    @27
    @38
    vz
    cS
    @26
    cB
    @6
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
    @23
    cC
    cle
    wph
    @30
    @37
    cA
    @23
    cle
    wbr
    @44
    @41
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
    @23
    cB
    cle
    ivth.11
    wph
    @23
    cB
    cle
    wbr
    #
    @39
    @42
    wph
    @30
    @34
    @47
    @39
    wb
    @44
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
    @33
    @34
    @19
    @20
    @21
    @22
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
    @1
    @17
    wph
    @0
    cr
    wcel
    #
    cU
    cr
    wcel
    #
    @1
    @17
    wb
    wph
    @19
    @31
    cr
    wcel
    #
    vx
    @18
    wral
    #
    @50
    @49
    wph
    @52
    vx
    @18
    ivth.8
    ralrimiva
    #
    @52
    @50
    vx
    cC
    @18
    @26
    cC
    wceq
    @31
    @0
    cr
    @26
    cC
    cF
    fveq2
    eleq1d
    rspcv
    sylc
    #
    ivth.3
    @0
    cU
    difrp
    syl2anc
    biimpa
    vz
    vy
    cD
    cc
    cC
    @9
    cF
    cncfi
    syl3anc
    @2
    @12
    @14
    vz
    crp
    @2
    @6
    crp
    wcel
    #
    wa
    #
    @12
    @11
    vy
    @18
    wral
    #
    @14
    wph
    @12
    @58
    wi
    #
    @1
    @56
    wph
    @18
    cD
    wss
    @59
    ivth.5
    @11
    vy
    @18
    cD
    ssralv
    syl
    ad2antrr
    @57
    @58
    @7
    cC
    @3
    clt
    wbr
    #
    wa
    #
    vy
    @18
    wrex
    #
    @14
    @57
    cB
    cC
    @6
    c2
    cdiv
    co
    #
    caddc
    co
    #
    cle
    wbr
    #
    cB
    @64
    cif
    #
    @18
    wcel
    #
    @66
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    @6
    clt
    wbr
    #
    cC
    @66
    clt
    wbr
    #
    @62
    @57
    @67
    @66
    cr
    wcel
    #
    cA
    @66
    cle
    wbr
    #
    @66
    cB
    cle
    wbr
    #
    @57
    @65
    cB
    @64
    cr
    wph
    @34
    @1
    @56
    ivth.2
    ad2antrr
    #
    @57
    cC
    @63
    wph
    @20
    @1
    @56
    @45
    ad2antrr
    #
    @57
    @63
    @56
    @63
    crp
    wcel
    @2
    @6
    rphalfcl
    adantl
    #
    rpred
    #
    readdcld
    #
    ifcld
    #
    @57
    cA
    cC
    @66
    wph
    @33
    @1
    @56
    ivth.1
    ad2antrr
    @76
    @80
    wph
    @21
    @1
    @56
    @46
    ad2antrr
    @57
    cC
    @66
    @76
    @80
    @57
    cC
    cB
    clt
    wbr
    #
    cC
    @64
    clt
    wbr
    #
    @71
    @57
    @0
    cB
    cF
    cfv
    #
    clt
    wbr
    #
    @81
    @2
    @84
    @56
    wph
    @1
    @84
    wph
    @1
    cU
    @83
    clt
    wbr
    #
    @84
    wph
    cA
    cF
    cfv
    cU
    clt
    wbr
    @85
    ivth.9
    simprd
    wph
    @50
    @51
    @83
    cr
    wcel
    #
    @1
    @85
    wa
    @84
    wi
    @55
    ivth.3
    wph
    cB
    @18
    wcel
    #
    @53
    @86
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    cA
    cB
    cle
    wbr
    @87
    wph
    cA
    ivth.1
    rexrd
    wph
    cB
    ivth.2
    rexrd
    wph
    cA
    cB
    ivth.1
    ivth.2
    ivth.4
    ltled
    cA
    cB
    ubicc2
    syl3anc
    @54
    @52
    @86
    vx
    cB
    @18
    @43
    @31
    @83
    cr
    @26
    cB
    cF
    fveq2
    eleq1d
    rspcv
    sylc
    @0
    cU
    @83
    lttr
    syl3anc
    mpan2d
    imp
    adantr
    wph
    @84
    @81
    wi
    @1
    @56
    wph
    @84
    @22
    cB
    cC
    wne
    #
    wa
    @81
    wph
    @84
    @88
    @22
    wph
    @84
    cB
    cC
    wph
    @84
    wn
    cB
    cC
    wceq
    #
    @0
    @0
    clt
    wbr
    #
    wn
    wph
    @0
    @55
    ltnrd
    @89
    @84
    @90
    @89
    @83
    @0
    @0
    clt
    cB
    cC
    cF
    fveq2
    breq2d
    notbid
    syl5ibrcom
    necon2ad
    @48
    jctild
    wph
    cC
    cB
    @45
    ivth.2
    ltlend
    sylibrd
    ad2antrr
    mpd
    @57
    cC
    @63
    @76
    @77
    ltaddrpd
    @65
    @81
    @82
    @71
    cB
    @64
    cB
    @66
    cC
    clt
    breq2
    @64
    @66
    cC
    clt
    breq2
    ifboth
    syl2anc
    #
    ltled
    #
    letrd
    @57
    @34
    @64
    cr
    wcel
    #
    @74
    @75
    @79
    cB
    @64
    min1
    syl2anc
    wph
    @67
    @72
    @73
    @74
    w3a
    wb
    #
    @1
    @56
    wph
    @33
    @34
    @94
    ivth.1
    ivth.2
    cA
    cB
    @66
    elicc2
    syl2anc
    ad2antrr
    mpbir3and
    @57
    @69
    @68
    @6
    clt
    @57
    cC
    @66
    @76
    @80
    @92
    abssubge0d
    @57
    @68
    @6
    clt
    wbr
    @66
    cC
    @6
    caddc
    co
    #
    clt
    wbr
    @57
    @66
    @64
    @95
    @80
    @79
    @57
    cC
    @6
    @76
    @56
    @6
    cr
    wcel
    @2
    @6
    rpre
    adantl
    #
    readdcld
    @57
    @34
    @93
    @66
    @64
    cle
    wbr
    @75
    @79
    cB
    @64
    min2
    syl2anc
    @57
    @63
    @6
    cC
    @78
    @96
    @76
    @56
    @63
    @6
    clt
    wbr
    @2
    @6
    rphalflt
    adantl
    ltadd2dd
    lelttrd
    @57
    @66
    cC
    @6
    @80
    @76
    @96
    ltsubadd2d
    mpbird
    eqbrtrd
    @91
    @61
    @70
    @71
    wa
    vy
    @66
    @18
    @3
    @66
    wceq
    #
    @7
    @70
    @60
    @71
    @97
    @5
    @69
    @6
    clt
    @97
    @4
    @68
    cabs
    @3
    @66
    cC
    cmin
    oveq1
    fveq2d
    breq1d
    @3
    @66
    cC
    clt
    breq2
    anbi12d
    rspcev
    syl12anc
    @58
    @62
    wa
    @11
    @61
    wa
    #
    vy
    @18
    wrex
    @57
    @14
    @11
    @61
    vy
    @18
    r19.29
    @57
    @98
    @14
    vy
    @18
    @98
    @10
    @60
    wa
    #
    @57
    @3
    @18
    wcel
    #
    wa
    #
    @14
    @11
    @61
    @99
    @7
    @10
    @60
    pm3.45
    imp
    @101
    @10
    @60
    @14
    @101
    @60
    @10
    @14
    @57
    @100
    @60
    @10
    @14
    wi
    @57
    @100
    @60
    wa
    #
    wa
    #
    @10
    @14
    @103
    @10
    @60
    @57
    @100
    @60
    simprr
    @103
    @10
    @0
    @9
    cmin
    co
    @8
    clt
    wbr
    #
    @8
    @0
    @9
    caddc
    co
    #
    clt
    wbr
    #
    wa
    @60
    wn
    #
    @103
    @8
    @0
    @9
    @103
    @100
    @53
    @8
    cr
    wcel
    #
    @57
    @100
    @60
    simprl
    #
    @103
    wph
    @53
    wph
    @1
    @56
    @102
    simplll
    #
    @54
    syl
    @52
    @108
    vx
    @3
    @18
    @26
    @3
    wceq
    #
    @31
    @8
    cr
    @26
    @3
    cF
    fveq2
    #
    eleq1d
    rspcv
    sylc
    #
    @103
    wph
    @50
    @110
    @55
    syl
    #
    @103
    cU
    @0
    @103
    wph
    @51
    @110
    ivth.3
    syl
    #
    @114
    resubcld
    absdifltd
    @103
    @106
    @107
    @104
    @103
    @106
    @3
    cS
    wcel
    #
    @107
    @103
    @8
    cU
    clt
    wbr
    #
    @8
    cU
    cle
    wbr
    #
    @106
    @116
    @103
    @108
    @51
    @117
    @118
    wi
    @113
    @115
    @8
    cU
    ltle
    syl2anc
    @103
    @105
    cU
    @8
    clt
    @103
    @0
    cU
    @103
    @0
    @114
    recnd
    @103
    cU
    @115
    recnd
    pncan3d
    breq2d
    @100
    @116
    @118
    wb
    @57
    @60
    @116
    @100
    @118
    @32
    @118
    vx
    @3
    @18
    cS
    @111
    @31
    @8
    cU
    cle
    @112
    breq1d
    ivth.10
    elrab2
    baib
    ad2antrl
    3imtr4d
    @103
    @116
    @3
    cC
    cle
    wbr
    #
    @107
    @103
    wph
    @30
    @116
    @119
    wi
    @110
    @44
    @30
    @116
    @119
    @30
    @116
    wa
    @3
    @23
    cC
    cle
    vx
    vz
    cS
    @3
    suprub
    ivth.11
    syl6breqr
    ex
    3syl
    @103
    @3
    cC
    @103
    @18
    cr
    @3
    @103
    wph
    @35
    @110
    @36
    syl
    @109
    sseldd
    @103
    wph
    @20
    @110
    @45
    syl
    lenltd
    sylibd
    syld
    adantld
    sylbid
    mt2d
    pm2.21d
    expr
    com23
    impd
    syl5
    rexlimdva
    syl5
    mpan2d
    syld
    rexlimdva
    mpd
    pm2.01da
end
