include "cv.mm"
include "cfv.mm"
include "c2nd.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cn.mm"
include "crab.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "wceq.mm"
include "cr.mm"
include "ssrab2.mm"
include "nnssre.mm"
include "sstri.mm"
include "wcel.mm"
include "sseli.mm"
include "wa.mm"
include "cxp.mm"
include "wf.mm"
include "cin.mm"
include "wss.mm"
include "inss2.mm"
include "fss.mm"
include "sylancl.mm"
include "adantr.mm"
include "c1.mm"
include "nnuz.mm"
include "1zzd.mm"
include "algrf.mm"
include "cicc.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "eqsstri.mm"
include "ffvelrn.mm"
include "sylancom.mm"
include "ffvelrnd.mm"
include "xp2nd.mm"
include "syl.mm"
include "sylan2.mm"
include "clt.mm"
include "wi.mm"
include "ad2antll.mm"
include "anim2i.mm"
include "adantrr.mm"
include "breq1.mm"
include "ralbidv.mm"
include "elrab.mm"
include "simprbi.mm"
include "caddc.mm"
include "breq2.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "wn.mm"
include "nnnlt1.mm"
include "adantl.mm"
include "pm2.21d.mm"
include "a1d.mm"
include "nnre.mm"
include "lep1d.mm"
include "peano2re.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "ralimdva.mm"
include "imim1d.mm"
include "wo.mm"
include "wb.mm"
include "simplr.mm"
include "simprl.mm"
include "nnleltp1.mm"
include "syl2anc.mm"
include "nnred.mm"
include "leloed.mm"
include "bitr3d.mm"
include "c1st.mm"
include "w3a.mm"
include "cif.mm"
include "simpll.mm"
include "ltp1.mm"
include "ltnle.mm"
include "mpdan.mm"
include "mpbid.mm"
include "rspccv.mm"
include "mtod.mm"
include "ovolicc2lem2.mm"
include "syl12anc.mm"
include "iftrued.mm"
include "ad2antrr.mm"
include "ralrimiva.mm"
include "breq1d.mm"
include "ifbieq1d.mm"
include "eleq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "eqeltrrd.mm"
include "algrp1.mm"
include "ad2ant2r.mm"
include "eleqtrrd.mm"
include "peano2nnd.mm"
include "ovolicc2lem1.mm"
include "simp3d.mm"
include "lttr.mm"
include "mpan2d.mm"
include "imim2d.mm"
include "com23.mm"
include "syl5ibrcom.mm"
include "a1dd.mm"
include "jaod.mm"
include "sylbid.mm"
include "expr.mm"
include "a2d.mm"
include "syld.mm"
include "expcom.mm"
include "nnind.mm"
include "syl3c.mm"
include "eqord1.mm"

theorem ovolicc2lem3
  let wph: wff ph
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let cT: class T
  let cU: class U
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cN: class N
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vi: setvar i
  let vj: setvar j
  let cM: class M
  let cX: class X
  assume ovolicc.1: |- ( ph -> A e. RR )
  assume ovolicc.2: |- ( ph -> B e. RR )
  assume ovolicc.3: |- ( ph -> A <_ B )
  assume ovolicc2.4: |- S = seq 1 ( + , ( ( abs o. - ) o. F ) )
  assume ovolicc2.5: |- ( ph -> F : NN --> ( <_ i^i ( RR X. RR ) ) )
  assume ovolicc2.6: |- ( ph -> U e. ( ~P ran ( (,) o. F ) i^i Fin ) )
  assume ovolicc2.7: |- ( ph -> ( A [,] B ) C_ U. U )
  assume ovolicc2.8: |- ( ph -> G : U --> NN )
  assume ovolicc2.9: |- ( ( ph /\ t e. U ) -> ( ( (,) o. F ) ` ( G ` t ) ) = t )
  assume ovolicc2.10: |- T = { u e. U | ( u i^i ( A [,] B ) ) =/= (/) }
  assume ovolicc2.11: |- ( ph -> H : T --> T )
  assume ovolicc2.12: |- ( ( ph /\ t e. T ) -> if ( ( 2nd ` ( F ` ( G ` t ) ) ) <_ B , ( 2nd ` ( F ` ( G ` t ) ) ) , B ) e. ( H ` t ) )
  assume ovolicc2.13: |- ( ph -> A e. C )
  assume ovolicc2.14: |- ( ph -> C e. T )
  assume ovolicc2.15: |- K = seq 1 ( ( H o. 1st ) , ( NN X. { C } ) )
  assume ovolicc2.16: |- W = { n e. NN | B e. ( K ` n ) }

  disjoint m n
  disjoint m t
  disjoint m u
  disjoint A m
  disjoint n t
  disjoint n u
  disjoint A n
  disjoint t u
  disjoint A t
  disjoint A u
  disjoint B m
  disjoint B n
  disjoint B t
  disjoint B u
  disjoint H t
  disjoint C m
  disjoint C n
  disjoint C t
  disjoint F n
  disjoint F t
  disjoint K n
  disjoint K t
  disjoint K u
  disjoint G n
  disjoint G t
  disjoint W m
  disjoint W n
  disjoint m ph
  disjoint n ph
  disjoint ph t
  disjoint T n
  disjoint T t
  disjoint N n
  disjoint N t
  disjoint N u
  disjoint U n
  disjoint U t
  disjoint U u
  disjoint f g
  disjoint f h
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g h
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint h k
  disjoint h m
  disjoint h n
  disjoint h t
  disjoint h u
  disjoint h v
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint A h
  disjoint k m
  disjoint k n
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint m v
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n v
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint B k
  disjoint B v
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C f
  disjoint C g
  disjoint C k
  disjoint C y
  disjoint C z
  disjoint h i
  disjoint h j
  disjoint F h
  disjoint i j
  disjoint i k
  disjoint i n
  disjoint i t
  disjoint i x
  disjoint i y
  disjoint F i
  disjoint j k
  disjoint j n
  disjoint j t
  disjoint j x
  disjoint j y
  disjoint F j
  disjoint F k
  disjoint F x
  disjoint F y
  disjoint i u
  disjoint i z
  disjoint K i
  disjoint j u
  disjoint j z
  disjoint K j
  disjoint K k
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint f i
  disjoint f j
  disjoint G f
  disjoint G h
  disjoint G i
  disjoint G j
  disjoint G k
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint i m
  disjoint M i
  disjoint j m
  disjoint M j
  disjoint M m
  disjoint M n
  disjoint M t
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint W i
  disjoint W j
  disjoint W k
  disjoint W x
  disjoint W y
  disjoint P k
  disjoint P y
  disjoint f ph
  disjoint g i
  disjoint g j
  disjoint g ph
  disjoint h ph
  disjoint i v
  disjoint i ph
  disjoint j v
  disjoint j ph
  disjoint k ph
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint T f
  disjoint T h
  disjoint T k
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint N k
  disjoint N x
  disjoint N y
  disjoint S h
  disjoint S z
  disjoint U h
  disjoint U x
  disjoint U z
  disjoint X t
  assert |- ( ( ph /\ ( N e. { n e. NN | A. m e. W n <_ m } /\ P e. { n e. NN | A. m e. W n <_ m } ) ) -> ( N = P <-> ( 2nd ` ( F ` ( G ` ( K ` N ) ) ) ) = ( 2nd ` ( F ` ( G ` ( K ` P ) ) ) ) ) )

  proof
    wph
    vy
    vk
    vy
    cv
    #
    cK
    cfv
    #
    cG
    cfv
    #
    cF
    cfv
    #
    c2nd
    cfv
    #
    vk
    cv
    #
    cK
    cfv
    #
    cG
    cfv
    #
    cF
    cfv
    #
    c2nd
    cfv
    #
    cN
    cP
    vn
    cv
    #
    vm
    cv
    #
    cle
    wbr
    #
    vm
    cW
    wral
    #
    vn
    cn
    crab
    #
    cN
    cK
    cfv
    #
    cG
    cfv
    #
    cF
    cfv
    #
    c2nd
    cfv
    cP
    cK
    cfv
    #
    cG
    cfv
    #
    cF
    cfv
    #
    c2nd
    cfv
    vy
    vk
    weq
    #
    @3
    @8
    c2nd
    @21
    @2
    @7
    cF
    @21
    @1
    @6
    cG
    @0
    @5
    cK
    fveq2
    fveq2d
    fveq2d
    fveq2d
    #
    @0
    cN
    wceq
    #
    @3
    @17
    c2nd
    @23
    @2
    @16
    cF
    @23
    @1
    @15
    cG
    @0
    cN
    cK
    fveq2
    fveq2d
    fveq2d
    fveq2d
    @0
    cP
    wceq
    #
    @3
    @20
    c2nd
    @24
    @2
    @19
    cF
    @24
    @1
    @18
    cG
    @0
    cP
    cK
    fveq2
    fveq2d
    fveq2d
    fveq2d
    @14
    cn
    cr
    @13
    vn
    cn
    ssrab2
    #
    nnssre
    sstri
    @0
    @14
    wcel
    #
    wph
    @0
    cn
    wcel
    #
    @4
    cr
    wcel
    #
    @14
    cn
    @0
    @25
    sseli
    #
    wph
    @27
    wa
    #
    @3
    cr
    cr
    cxp
    #
    wcel
    @28
    @30
    cn
    @31
    @2
    cF
    wph
    cn
    @31
    cF
    wf
    #
    @27
    wph
    cn
    cle
    @31
    cin
    #
    cF
    wf
    @33
    @31
    wss
    @32
    ovolicc2.5
    cle
    @31
    inss2
    cn
    @33
    @31
    cF
    fss
    sylancl
    #
    adantr
    @30
    cU
    cn
    @1
    cG
    wph
    cU
    cn
    cG
    wf
    #
    @27
    ovolicc2.8
    adantr
    wph
    @27
    cn
    cU
    cK
    wf
    #
    @1
    cU
    wcel
    @30
    cn
    cT
    cK
    wf
    #
    cT
    cU
    wss
    #
    @36
    wph
    @37
    @27
    wph
    cC
    cK
    cT
    cH
    c1
    cn
    nnuz
    ovolicc2.15
    wph
    1zzd
    #
    ovolicc2.14
    ovolicc2.11
    algrf
    #
    adantr
    cT
    vu
    cv
    cA
    cB
    cicc
    co
    cin
    c0
    wne
    #
    vu
    cU
    crab
    cU
    ovolicc2.10
    @41
    vu
    cU
    ssrab2
    eqsstri
    #
    cn
    cT
    cU
    cK
    fss
    #
    sylancl
    cn
    cU
    @0
    cK
    ffvelrn
    sylancom
    ffvelrnd
    ffvelrnd
    @3
    cr
    cr
    xp2nd
    syl
    #
    sylan2
    wph
    @26
    @5
    @14
    wcel
    #
    wa
    wa
    @5
    cn
    wcel
    #
    @30
    @5
    @11
    cle
    wbr
    #
    vm
    cW
    wral
    #
    @0
    @5
    clt
    wbr
    #
    @4
    @9
    clt
    wbr
    #
    wi
    #
    @45
    @46
    wph
    @26
    @14
    cn
    @5
    @25
    sseli
    ad2antll
    wph
    @26
    @30
    @45
    @26
    @27
    wph
    @29
    anim2i
    adantrr
    @45
    @48
    wph
    @26
    @45
    @46
    @48
    @13
    @48
    vn
    @5
    cn
    vn
    vk
    weq
    @12
    @47
    vm
    cW
    @10
    @5
    @11
    cle
    breq1
    ralbidv
    elrab
    simprbi
    ad2antll
    @30
    vx
    cv
    #
    @11
    cle
    wbr
    #
    vm
    cW
    wral
    #
    @0
    @52
    clt
    wbr
    #
    @4
    @52
    cK
    cfv
    #
    cG
    cfv
    #
    cF
    cfv
    #
    c2nd
    cfv
    #
    clt
    wbr
    #
    wi
    #
    wi
    #
    wi
    @30
    c1
    @11
    cle
    wbr
    #
    vm
    cW
    wral
    #
    @0
    c1
    clt
    wbr
    #
    @4
    c1
    cK
    cfv
    #
    cG
    cfv
    #
    cF
    cfv
    #
    c2nd
    cfv
    #
    clt
    wbr
    #
    wi
    #
    wi
    #
    wi
    @30
    @48
    @51
    wi
    #
    wi
    #
    @30
    @5
    c1
    caddc
    co
    #
    @11
    cle
    wbr
    #
    vm
    cW
    wral
    #
    @0
    @75
    clt
    wbr
    #
    @4
    @75
    cK
    cfv
    #
    cG
    cfv
    #
    cF
    cfv
    #
    c2nd
    cfv
    #
    clt
    wbr
    #
    wi
    #
    wi
    #
    wi
    @74
    vx
    vk
    @5
    @52
    c1
    wceq
    #
    @62
    @72
    @30
    @86
    @54
    @64
    @61
    @71
    @86
    @53
    @63
    vm
    cW
    @52
    c1
    @11
    cle
    breq1
    ralbidv
    @86
    @55
    @65
    @60
    @70
    @52
    c1
    @0
    clt
    breq2
    @86
    @59
    @69
    @4
    clt
    @86
    @58
    @68
    c2nd
    @86
    @57
    @67
    cF
    @86
    @56
    @66
    cG
    @52
    c1
    cK
    fveq2
    fveq2d
    fveq2d
    fveq2d
    breq2d
    imbi12d
    imbi12d
    imbi2d
    vx
    vk
    weq
    #
    @62
    @73
    @30
    @87
    @54
    @48
    @61
    @51
    @87
    @53
    @47
    vm
    cW
    @52
    @5
    @11
    cle
    breq1
    ralbidv
    @87
    @55
    @49
    @60
    @50
    @52
    @5
    @0
    clt
    breq2
    @87
    @59
    @9
    @4
    clt
    @87
    @58
    @8
    c2nd
    @87
    @57
    @7
    cF
    @87
    @56
    @6
    cG
    @52
    @5
    cK
    fveq2
    fveq2d
    fveq2d
    fveq2d
    breq2d
    imbi12d
    imbi12d
    imbi2d
    #
    @52
    @75
    wceq
    #
    @62
    @85
    @30
    @89
    @54
    @77
    @61
    @84
    @89
    @53
    @76
    vm
    cW
    @52
    @75
    @11
    cle
    breq1
    ralbidv
    @89
    @55
    @78
    @60
    @83
    @52
    @75
    @0
    clt
    breq2
    @89
    @59
    @82
    @4
    clt
    @89
    @58
    @81
    c2nd
    @89
    @57
    @80
    cF
    @89
    @56
    @79
    cG
    @52
    @75
    cK
    fveq2
    fveq2d
    fveq2d
    fveq2d
    breq2d
    imbi12d
    imbi12d
    imbi2d
    @88
    @30
    @71
    @64
    @30
    @65
    @70
    @27
    @65
    wn
    wph
    @0
    nnnlt1
    adantl
    pm2.21d
    a1d
    @46
    @30
    @73
    @85
    @30
    @46
    @73
    @85
    wi
    @30
    @46
    wa
    #
    @73
    @77
    @51
    wi
    #
    @85
    @46
    @73
    @91
    wi
    @30
    @46
    @77
    @48
    @51
    @46
    @76
    @47
    vm
    cW
    @46
    @11
    cW
    wcel
    #
    wa
    #
    @5
    @75
    cle
    wbr
    #
    @76
    @47
    @93
    @5
    @46
    @5
    cr
    wcel
    #
    @92
    @5
    nnre
    adantr
    #
    lep1d
    @93
    @95
    @75
    cr
    wcel
    #
    @11
    cr
    wcel
    #
    @94
    @76
    wa
    @47
    wi
    @96
    @93
    @95
    @97
    @96
    @5
    peano2re
    #
    syl
    @92
    @98
    @46
    cW
    cr
    @11
    cW
    cn
    cr
    cW
    cB
    @10
    cK
    cfv
    wcel
    #
    vn
    cn
    crab
    cn
    ovolicc2.16
    @100
    vn
    cn
    ssrab2
    eqsstri
    nnssre
    sstri
    sseli
    adantl
    @5
    @75
    @11
    letr
    syl3anc
    mpand
    ralimdva
    imim1d
    adantl
    @90
    @77
    @51
    @84
    @30
    @46
    @77
    @51
    @84
    wi
    @30
    @46
    @77
    wa
    #
    wa
    #
    @78
    @51
    @83
    @102
    @78
    @49
    @21
    wo
    #
    @51
    @83
    wi
    #
    @102
    @0
    @5
    cle
    wbr
    #
    @78
    @103
    @102
    @27
    @46
    @105
    @78
    wb
    wph
    @27
    @101
    simplr
    #
    @30
    @46
    @77
    simprl
    #
    @0
    @5
    nnleltp1
    syl2anc
    @102
    @0
    @5
    @102
    @0
    @106
    nnred
    @102
    @5
    @107
    nnred
    #
    leloed
    bitr3d
    @102
    @49
    @104
    @21
    @102
    @51
    @49
    @83
    @102
    @50
    @83
    @49
    @102
    @50
    @9
    @82
    clt
    wbr
    #
    @83
    @102
    @9
    cr
    wcel
    #
    @81
    c1st
    cfv
    @9
    clt
    wbr
    #
    @109
    @102
    @9
    @79
    wcel
    #
    @110
    @111
    @109
    w3a
    #
    @102
    @9
    @6
    cH
    cfv
    #
    @79
    @102
    @9
    cB
    cle
    wbr
    #
    @9
    cB
    cif
    #
    @9
    @114
    @102
    @115
    @9
    cB
    @102
    wph
    @46
    @5
    cW
    wcel
    #
    wn
    @115
    wph
    @27
    @101
    simpll
    #
    @107
    @102
    @117
    @75
    @5
    cle
    wbr
    #
    @102
    @95
    @119
    wn
    #
    @108
    @95
    @5
    @75
    clt
    wbr
    #
    @120
    @5
    ltp1
    @95
    @97
    @121
    @120
    wb
    @99
    @5
    @75
    ltnle
    mpdan
    mpbid
    syl
    @77
    @117
    @119
    wi
    @30
    @46
    @76
    @119
    vm
    @5
    cW
    @11
    @5
    @75
    cle
    breq2
    rspccv
    ad2antll
    mtod
    wph
    vu
    vt
    cA
    cB
    cC
    cS
    cT
    cU
    vn
    cF
    cG
    cH
    cK
    @5
    cW
    ovolicc.1
    ovolicc.2
    ovolicc.3
    ovolicc2.4
    ovolicc2.5
    ovolicc2.6
    ovolicc2.7
    ovolicc2.8
    ovolicc2.9
    ovolicc2.10
    ovolicc2.11
    ovolicc2.12
    ovolicc2.13
    ovolicc2.14
    ovolicc2.15
    ovolicc2.16
    ovolicc2lem2
    syl12anc
    iftrued
    @102
    @6
    cT
    wcel
    vt
    cv
    #
    cG
    cfv
    #
    cF
    cfv
    #
    c2nd
    cfv
    #
    cB
    cle
    wbr
    #
    @125
    cB
    cif
    #
    @122
    cH
    cfv
    #
    wcel
    #
    vt
    cT
    wral
    #
    @116
    @114
    wcel
    #
    @102
    cn
    cT
    @5
    cK
    wph
    @37
    @27
    @101
    @40
    ad2antrr
    #
    @107
    ffvelrnd
    wph
    @130
    @27
    @101
    wph
    @129
    vt
    cT
    ovolicc2.12
    ralrimiva
    ad2antrr
    @129
    @131
    vt
    @6
    cT
    @122
    @6
    wceq
    #
    @127
    @116
    @128
    @114
    @133
    @126
    @115
    @125
    @9
    cB
    @133
    @125
    @9
    cB
    cle
    @133
    @124
    @8
    c2nd
    @133
    @123
    @7
    cF
    @122
    @6
    cG
    fveq2
    fveq2d
    fveq2d
    #
    breq1d
    @134
    ifbieq1d
    @122
    @6
    cH
    fveq2
    eleq12d
    rspcv
    sylc
    eqeltrrd
    wph
    @46
    @79
    @114
    wceq
    @27
    @77
    wph
    cC
    cK
    cT
    cH
    @5
    c1
    cn
    nnuz
    ovolicc2.15
    @39
    ovolicc2.14
    ovolicc2.11
    algrp1
    ad2ant2r
    eleqtrrd
    @102
    wph
    @79
    cU
    wcel
    @112
    @113
    wb
    @118
    @102
    cn
    cU
    @75
    cK
    @102
    @37
    @38
    @36
    @132
    @42
    @43
    sylancl
    #
    @102
    @5
    @107
    peano2nnd
    ffvelrnd
    #
    wph
    vt
    cA
    cB
    @9
    cS
    cU
    cF
    cG
    @79
    ovolicc.1
    ovolicc.2
    ovolicc.3
    ovolicc2.4
    ovolicc2.5
    ovolicc2.6
    ovolicc2.7
    ovolicc2.8
    ovolicc2.9
    ovolicc2lem1
    syl2anc
    mpbid
    simp3d
    #
    @102
    @28
    @110
    @82
    cr
    wcel
    #
    @50
    @109
    wa
    @83
    wi
    @30
    @28
    @101
    @44
    adantr
    @102
    @8
    @31
    wcel
    @110
    @102
    cn
    @31
    @7
    cF
    wph
    @32
    @27
    @101
    @34
    ad2antrr
    #
    @102
    cU
    cn
    @6
    cG
    wph
    @35
    @27
    @101
    ovolicc2.8
    ad2antrr
    #
    @102
    cn
    cU
    @5
    cK
    @135
    @107
    ffvelrnd
    ffvelrnd
    ffvelrnd
    @8
    cr
    cr
    xp2nd
    syl
    @102
    @81
    @31
    wcel
    @138
    @102
    cn
    @31
    @80
    cF
    @139
    @102
    cU
    cn
    @79
    cG
    @140
    @136
    ffvelrnd
    ffvelrnd
    @81
    cr
    cr
    xp2nd
    syl
    @4
    @9
    @82
    lttr
    syl3anc
    mpan2d
    imim2d
    com23
    @102
    @21
    @83
    @51
    @102
    @83
    @21
    @109
    @137
    @21
    @4
    @9
    @82
    clt
    @22
    breq1d
    syl5ibrcom
    a1dd
    jaod
    sylbid
    com23
    expr
    a2d
    syld
    expcom
    a2d
    nnind
    syl3c
    eqord1
end
