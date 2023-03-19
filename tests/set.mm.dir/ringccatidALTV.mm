include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "chom.mm"
include "cfv.mm"
include "co.mm"
include "w3a.mm"
include "cco.mm"
include "cid.mm"
include "cbs.mm"
include "cres.mm"
include "cvv.mm"
include "wceq.mm"
include "a1i.mm"
include "eqidd.mm"
include "cringcALTV.mm"
include "fvex.mm"
include "eqeltri.mm"
include "biid.mm"
include "crh.mm"
include "crg.mm"
include "cin.mm"
include "simpl.mm"
include "ringcbasALTV.mm"
include "wi.mm"
include "eleq2.mm"
include "elin.mm"
include "simprbi.mm"
include "syl6bi.mm"
include "com12.mm"
include "adantl.mm"
include "mpd.mm"
include "eqid.mm"
include "idrhm.mm"
include "syl.mm"
include "simpr.mm"
include "ringchomALTV.mm"
include "eleqtrrd.mm"
include "cop.mm"
include "ccom.mm"
include "3ad2ant1.mm"
include "simp1.mm"
include "3ad2ant3.mm"
include "eleq2d.mm"
include "biimpd.mm"
include "3exp.mm"
include "com14.mm"
include "com13.mm"
include "3imp.mm"
include "impcom.mm"
include "expcom.mm"
include "ringccoALTV.mm"
include "wf.mm"
include "simprl.mm"
include "simprr.mm"
include "elringchomALTV.mm"
include "ex.mm"
include "fcoi2.mm"
include "syl8.mm"
include "a1d.mm"
include "eqtrd.mm"
include "simp3.mm"
include "adantr.mm"
include "3ad2ant2.mm"
include "fcoi1.mm"
include "expdcom.mm"
include "rhmco.mm"
include "syl2anc.mm"
include "3eltr4d.mm"
include "coass.mm"
include "simp2r.mm"
include "3eqtr4a.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "iscatd2.mm"

theorem ringccatidALTV
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cU: class U
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let wph: wff ph
  let cX: class X
  let vk: setvar k
  assume ringccatALTV.c: |- C = ( RingCatALTV ` U )
  assume ringccatidALTV.b: |- B = ( Base ` C )

  disjoint B x
  disjoint C x
  disjoint U x
  disjoint V x
  disjoint f g
  disjoint f h
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint g h
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint B g
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint B h
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint C w
  disjoint C y
  disjoint C z
  disjoint U f
  disjoint U g
  disjoint U h
  disjoint U w
  disjoint U y
  disjoint U z
  disjoint V f
  disjoint V g
  disjoint V h
  disjoint V w
  disjoint V y
  disjoint V z
  disjoint ph x
  disjoint X x
  disjoint k x
  assert |- ( U e. V -> ( C e. Cat /\ ( Id ` C ) = ( x e. B |-> ( _I |` ( Base ` x ) ) ) ) )

  proof
    cU
    cV
    wcel
    #
    vw
    cv
    #
    cB
    wcel
    #
    vx
    cv
    #
    cB
    wcel
    #
    wa
    #
    vy
    cv
    #
    cB
    wcel
    #
    vz
    cv
    #
    cB
    wcel
    #
    wa
    #
    vf
    cv
    #
    @1
    @3
    cC
    chom
    cfv
    #
    co
    #
    wcel
    #
    vg
    cv
    #
    @3
    @6
    @12
    co
    #
    wcel
    #
    vh
    cv
    #
    @6
    @8
    @12
    co
    #
    wcel
    #
    w3a
    #
    w3a
    #
    vw
    vx
    vy
    vz
    cB
    cC
    cC
    cco
    cfv
    #
    cid
    @3
    cbs
    cfv
    #
    cres
    #
    vf
    vg
    vh
    @12
    cvv
    cB
    cC
    cbs
    cfv
    wceq
    @0
    ringccatidALTV.b
    a1i
    @0
    @12
    eqidd
    @0
    @23
    eqidd
    cC
    cvv
    wcel
    @0
    cC
    cU
    cringcALTV
    cfv
    cvv
    ringccatALTV.c
    cU
    cringcALTV
    fvex
    eqeltri
    a1i
    @22
    biid
    @0
    @4
    wa
    #
    @25
    @3
    @3
    crh
    co
    #
    @3
    @3
    @12
    co
    @26
    @3
    crg
    wcel
    #
    @25
    @27
    wcel
    #
    @26
    cB
    cU
    crg
    cin
    #
    wceq
    #
    @28
    @26
    cB
    cC
    cU
    cV
    ringccatALTV.c
    ringccatidALTV.b
    @0
    @4
    simpl
    #
    ringcbasALTV
    @4
    @31
    @28
    wi
    @0
    @31
    @4
    @28
    @31
    @4
    @3
    @30
    wcel
    #
    @28
    cB
    @30
    @3
    eleq2
    @33
    @3
    cU
    wcel
    @28
    @3
    cU
    crg
    elin
    simprbi
    syl6bi
    com12
    adantl
    mpd
    @24
    @3
    @24
    eqid
    idrhm
    syl
    #
    @26
    cB
    cC
    cU
    @12
    cV
    @3
    @3
    ringccatALTV.c
    ringccatidALTV.b
    @32
    @12
    eqid
    #
    @0
    @4
    simpr
    #
    @36
    ringchomALTV
    eleqtrrd
    @0
    @22
    wa
    #
    @25
    @11
    @1
    @3
    cop
    #
    @3
    @23
    co
    co
    @25
    @11
    ccom
    #
    @11
    @37
    cB
    cC
    @23
    cU
    @11
    @25
    cV
    @1
    @3
    @3
    ringccatALTV.c
    ringccatidALTV.b
    @0
    @22
    simpl
    #
    @23
    eqid
    #
    @22
    @2
    @0
    @5
    @10
    @2
    @21
    @2
    @4
    simpl
    #
    3ad2ant1
    adantl
    #
    @22
    @4
    @0
    @5
    @10
    @4
    @21
    @2
    @4
    simpr
    #
    3ad2ant1
    adantl
    #
    @45
    @22
    @0
    @11
    @1
    @3
    crh
    co
    #
    wcel
    #
    @5
    @10
    @21
    @0
    @47
    wi
    #
    @21
    @10
    @5
    @48
    @14
    @17
    @10
    @5
    @48
    wi
    wi
    @20
    @0
    @10
    @5
    @14
    @47
    @0
    @10
    @5
    @14
    @47
    wi
    @0
    @10
    @5
    w3a
    #
    @14
    @47
    @49
    @13
    @46
    @11
    @49
    cB
    cC
    cU
    @12
    cV
    @1
    @3
    ringccatALTV.c
    ringccatidALTV.b
    @0
    @10
    @5
    simp1
    #
    @35
    @5
    @0
    @2
    @10
    @42
    3ad2ant3
    @5
    @0
    @4
    @10
    @44
    3ad2ant3
    #
    ringchomALTV
    eleq2d
    biimpd
    3exp
    com14
    3ad2ant1
    com13
    3imp
    impcom
    #
    @22
    @0
    @29
    @5
    @10
    @0
    @29
    wi
    #
    @21
    @4
    @53
    @2
    @0
    @4
    @29
    @34
    expcom
    adantl
    #
    3ad2ant1
    impcom
    ringccoALTV
    @22
    @0
    @39
    @11
    wceq
    #
    @5
    @10
    @21
    @0
    @55
    wi
    #
    @5
    @21
    @56
    wi
    @10
    @21
    @5
    @56
    @14
    @17
    @5
    @56
    wi
    @20
    @14
    @5
    @0
    @1
    cbs
    cfv
    #
    @24
    @11
    wf
    #
    @55
    @0
    @5
    @14
    @58
    @0
    @5
    @14
    @58
    wi
    @0
    @5
    wa
    cB
    cC
    cU
    @11
    @12
    cV
    @1
    @3
    ringccatALTV.c
    ringccatidALTV.b
    @0
    @5
    simpl
    @35
    @0
    @2
    @4
    simprl
    @0
    @2
    @4
    simprr
    elringchomALTV
    ex
    com13
    @57
    @24
    @11
    fcoi2
    syl8
    3ad2ant1
    com12
    a1d
    3imp
    impcom
    eqtrd
    @22
    @0
    @15
    @25
    @3
    @3
    cop
    @6
    @23
    co
    co
    #
    @15
    wceq
    #
    @5
    @10
    @21
    @0
    @60
    wi
    #
    @21
    @5
    @10
    @61
    @17
    @14
    @5
    @10
    wa
    #
    @61
    wi
    @20
    @17
    @62
    @0
    @60
    @17
    @62
    @0
    w3a
    #
    @59
    @15
    @25
    ccom
    #
    @15
    @63
    cB
    cC
    @23
    cU
    @25
    @15
    cV
    @3
    @3
    @6
    ringccatALTV.c
    ringccatidALTV.b
    @17
    @62
    @0
    simp3
    @41
    @62
    @17
    @4
    @0
    @5
    @4
    @10
    @44
    adantr
    #
    3ad2ant2
    #
    @66
    @62
    @17
    @7
    @0
    @5
    @7
    @9
    simprl
    #
    3ad2ant2
    @17
    @62
    @0
    @29
    @62
    @53
    wi
    @17
    @5
    @53
    @10
    @54
    adantr
    a1i
    3imp
    @17
    @62
    @0
    @15
    @3
    @6
    crh
    co
    #
    wcel
    #
    @0
    @62
    @17
    @69
    @0
    @62
    @17
    @69
    wi
    #
    @0
    @62
    wa
    #
    @17
    @69
    @71
    @16
    @68
    @15
    @71
    cB
    cC
    cU
    @12
    cV
    @3
    @6
    ringccatALTV.c
    ringccatidALTV.b
    @0
    @62
    simpl
    #
    @35
    @62
    @4
    @0
    @65
    adantl
    #
    @62
    @7
    @0
    @67
    adantl
    #
    ringchomALTV
    eleq2d
    biimpd
    ex
    com13
    3imp
    ringccoALTV
    @63
    @24
    @6
    cbs
    cfv
    #
    @15
    wf
    #
    @64
    @15
    wceq
    @17
    @62
    @0
    @76
    @0
    @62
    @17
    @76
    @0
    @62
    @17
    @76
    wi
    @71
    cB
    cC
    cU
    @15
    @12
    cV
    @3
    @6
    ringccatALTV.c
    ringccatidALTV.b
    @72
    @35
    @73
    @74
    elringchomALTV
    ex
    com13
    3imp
    @24
    @75
    @15
    fcoi1
    syl
    eqtrd
    3exp
    3ad2ant2
    expdcom
    3imp
    impcom
    @37
    @15
    @11
    ccom
    #
    @1
    @6
    crh
    co
    #
    @15
    @11
    @38
    @6
    @23
    co
    co
    #
    @1
    @6
    @12
    co
    @37
    @69
    @47
    @77
    @78
    wcel
    @22
    @0
    @69
    @5
    @10
    @21
    @0
    @69
    wi
    #
    @21
    @10
    @5
    @80
    @17
    @14
    @10
    @5
    @80
    wi
    wi
    @20
    @0
    @10
    @5
    @17
    @69
    @0
    @10
    @5
    @70
    @49
    @17
    @69
    @49
    @16
    @68
    @15
    @49
    cB
    cC
    cU
    @12
    cV
    @3
    @6
    ringccatALTV.c
    ringccatidALTV.b
    @50
    @35
    @51
    @10
    @0
    @7
    @5
    @7
    @9
    simpl
    #
    3ad2ant2
    #
    ringchomALTV
    eleq2d
    biimpd
    3exp
    com14
    3ad2ant2
    com13
    3imp
    impcom
    #
    @52
    @1
    @3
    @6
    @15
    @11
    rhmco
    syl2anc
    #
    @37
    cB
    cC
    @23
    cU
    @11
    @15
    cV
    @1
    @3
    @6
    ringccatALTV.c
    ringccatidALTV.b
    @40
    @41
    @43
    @45
    @22
    @7
    @0
    @10
    @5
    @7
    @21
    @81
    3ad2ant2
    adantl
    #
    @52
    @83
    ringccoALTV
    #
    @37
    cB
    cC
    cU
    @12
    cV
    @1
    @6
    ringccatALTV.c
    ringccatidALTV.b
    @40
    @35
    @43
    @85
    ringchomALTV
    3eltr4d
    @37
    @18
    @15
    ccom
    #
    @11
    @38
    @8
    @23
    co
    #
    co
    #
    @18
    @77
    @1
    @6
    cop
    @8
    @23
    co
    #
    co
    #
    @18
    @15
    @3
    @6
    cop
    @8
    @23
    co
    co
    #
    @11
    @88
    co
    @18
    @79
    @90
    co
    @37
    @87
    @11
    ccom
    @18
    @77
    ccom
    @89
    @91
    @18
    @15
    @11
    coass
    @37
    cB
    cC
    @23
    cU
    @11
    @87
    cV
    @1
    @3
    @8
    ringccatALTV.c
    ringccatidALTV.b
    @40
    @41
    @43
    @45
    @22
    @9
    @0
    @5
    @7
    @9
    @21
    simp2r
    adantl
    #
    @52
    @37
    @18
    @6
    @8
    crh
    co
    #
    wcel
    #
    @69
    @87
    @3
    @8
    crh
    co
    wcel
    @22
    @0
    @95
    @5
    @10
    @21
    @0
    @95
    wi
    #
    @21
    @10
    @5
    @96
    @20
    @14
    @10
    @5
    @96
    wi
    wi
    @17
    @0
    @10
    @5
    @20
    @95
    @0
    @10
    @5
    @20
    @95
    wi
    @49
    @20
    @95
    @49
    @19
    @94
    @18
    @49
    cB
    cC
    cU
    @12
    cV
    @6
    @8
    ringccatALTV.c
    ringccatidALTV.b
    @50
    @35
    @82
    @0
    @7
    @9
    @5
    simp2r
    ringchomALTV
    eleq2d
    biimpd
    3exp
    com14
    3ad2ant3
    com13
    3imp
    impcom
    #
    @83
    @3
    @6
    @8
    @18
    @15
    rhmco
    syl2anc
    ringccoALTV
    @37
    cB
    cC
    @23
    cU
    @77
    @18
    cV
    @1
    @6
    @8
    ringccatALTV.c
    ringccatidALTV.b
    @40
    @41
    @43
    @85
    @93
    @84
    @97
    ringccoALTV
    3eqtr4a
    @37
    @92
    @87
    @11
    @88
    @37
    cB
    cC
    @23
    cU
    @15
    @18
    cV
    @3
    @6
    @8
    ringccatALTV.c
    ringccatidALTV.b
    @40
    @41
    @45
    @85
    @93
    @83
    @97
    ringccoALTV
    oveq1d
    @37
    @79
    @77
    @18
    @90
    @86
    oveq2d
    3eqtr4d
    iscatd2
end
