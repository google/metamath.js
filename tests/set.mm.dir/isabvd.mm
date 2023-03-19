include "cabv.mm"
include "cfv.mm"
include "wcel.mm"
include "cbs.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "wceq.mm"
include "c0g.mm"
include "wb.mm"
include "cmulr.mm"
include "cmul.mm"
include "cplusg.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wral.mm"
include "wfn.mm"
include "cr.mm"
include "feq2d.mm"
include "mpbid.mm"
include "ffn.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "0le0.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "syl5breqr.mm"
include "adantr.mm"
include "fveq2.mm"
include "breq2d.mm"
include "syl5ibrcom.mm"
include "wne.mm"
include "w3a.mm"
include "clt.mm"
include "simp1.mm"
include "simp2.mm"
include "3ad2ant1.mm"
include "eleqtrrd.mm"
include "simp3.mm"
include "neeqtrrd.mm"
include "syl3anc.mm"
include "wi.mm"
include "0re.mm"
include "3adant3.mm"
include "ltle.mm"
include "sylancr.mm"
include "mpd.mm"
include "3expia.mm"
include "pm2.61dne.mm"
include "elrege0.mm"
include "sylanbrc.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "gt0ne0d.mm"
include "necon4d.mm"
include "eqeq1d.mm"
include "impbid.mm"
include "oveq1.mm"
include "crg.mm"
include "eqid.mm"
include "ringlz.mm"
include "syl2anc.mm"
include "sylan9eqr.mm"
include "oveq1d.mm"
include "cc.mm"
include "ffvelrnd.mm"
include "recnd.mm"
include "mul02d.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"
include "oveq2.mm"
include "ringrz.mm"
include "oveq2d.mm"
include "mul01d.mm"
include "simpl1.mm"
include "oveqd.mm"
include "simpl2.mm"
include "simprl.mm"
include "simpl3.mm"
include "simprr.mm"
include "syl122anc.mm"
include "pm2.61da2ne.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "grplid.mm"
include "addge02d.mm"
include "eqbrtrd.mm"
include "grprid.mm"
include "addge01d.mm"
include "eqbrtrrd.mm"
include "jca.mm"
include "ralrimiv.mm"
include "isabv.mm"
include "mpbir2and.mm"

theorem isabvd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let c.0: class .0.
  assume isabvd.a: |- ( ph -> A = ( AbsVal ` R ) )
  assume isabvd.b: |- ( ph -> B = ( Base ` R ) )
  assume isabvd.p: |- ( ph -> .+ = ( +g ` R ) )
  assume isabvd.t: |- ( ph -> .x. = ( .r ` R ) )
  assume isabvd.z: |- ( ph -> .0. = ( 0g ` R ) )
  assume isabvd.1: |- ( ph -> R e. Ring )
  assume isabvd.2: |- ( ph -> F : B --> RR )
  assume isabvd.3: |- ( ph -> ( F ` .0. ) = 0 )
  assume isabvd.4: |- ( ( ph /\ x e. B /\ x =/= .0. ) -> 0 < ( F ` x ) )
  assume isabvd.5: |- ( ( ph /\ ( x e. B /\ x =/= .0. ) /\ ( y e. B /\ y =/= .0. ) ) -> ( F ` ( x .x. y ) ) = ( ( F ` x ) x. ( F ` y ) ) )
  assume isabvd.6: |- ( ( ph /\ ( x e. B /\ x =/= .0. ) /\ ( y e. B /\ y =/= .0. ) ) -> ( F ` ( x .+ y ) ) <_ ( ( F ` x ) + ( F ` y ) ) )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint ph x
  disjoint ph y
  disjoint R x
  disjoint R y
  assert |- ( ph -> F e. A )

  proof
    wph
    cF
    cR
    cabv
    cfv
    #
    cA
    wph
    cF
    @0
    wcel
    #
    cR
    cbs
    cfv
    #
    cc0
    cpnf
    cico
    co
    #
    cF
    wf
    #
    vx
    cv
    #
    cF
    cfv
    #
    cc0
    wceq
    #
    @5
    cR
    c0g
    cfv
    #
    wceq
    #
    wb
    #
    @5
    vy
    cv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cF
    cfv
    #
    @6
    @11
    cF
    cfv
    #
    cmul
    co
    #
    wceq
    #
    @5
    @11
    cR
    cplusg
    cfv
    #
    co
    #
    cF
    cfv
    #
    @6
    @15
    caddc
    co
    #
    cle
    wbr
    #
    wa
    #
    vy
    @2
    wral
    #
    wa
    #
    vx
    @2
    wral
    #
    wph
    cF
    @2
    wfn
    #
    @6
    @3
    wcel
    #
    vx
    @2
    wral
    @4
    wph
    @2
    cr
    cF
    wf
    #
    @27
    wph
    cB
    cr
    cF
    wf
    @29
    isabvd.2
    wph
    cB
    @2
    cr
    cF
    isabvd.b
    feq2d
    mpbid
    #
    @2
    cr
    cF
    ffn
    syl
    wph
    @28
    vx
    @2
    wph
    @5
    @2
    wcel
    #
    wa
    #
    @6
    cr
    wcel
    #
    cc0
    @6
    cle
    wbr
    #
    @28
    wph
    @2
    cr
    @5
    cF
    @30
    ffvelrnda
    #
    @32
    @34
    @5
    @8
    @32
    @34
    @9
    cc0
    @8
    cF
    cfv
    #
    cle
    wbr
    #
    wph
    @37
    @31
    wph
    cc0
    cc0
    @36
    cle
    0le0
    wph
    c.0
    cF
    cfv
    @36
    cc0
    wph
    c.0
    @8
    cF
    isabvd.z
    fveq2d
    isabvd.3
    eqtr3d
    #
    syl5breqr
    adantr
    @9
    @6
    @36
    cc0
    cle
    @5
    @8
    cF
    fveq2
    #
    breq2d
    syl5ibrcom
    wph
    @31
    @5
    @8
    wne
    #
    @34
    wph
    @31
    @40
    w3a
    #
    cc0
    @6
    clt
    wbr
    #
    @34
    @41
    wph
    @5
    cB
    wcel
    #
    @5
    c.0
    wne
    #
    @42
    wph
    @31
    @40
    simp1
    @41
    @5
    @2
    cB
    wph
    @31
    @40
    simp2
    wph
    @31
    cB
    @2
    wceq
    #
    @40
    isabvd.b
    3ad2ant1
    eleqtrrd
    @41
    @5
    @8
    c.0
    wph
    @31
    @40
    simp3
    wph
    @31
    c.0
    @8
    wceq
    #
    @40
    isabvd.z
    3ad2ant1
    neeqtrrd
    isabvd.4
    syl3anc
    #
    @41
    cc0
    cr
    wcel
    @33
    @42
    @34
    wi
    0re
    wph
    @31
    @33
    @40
    @35
    3adant3
    cc0
    @6
    ltle
    sylancr
    mpd
    3expia
    pm2.61dne
    @6
    elrege0
    sylanbrc
    ralrimiva
    vx
    @2
    @3
    cF
    ffnfv
    sylanbrc
    wph
    @25
    vx
    @2
    @32
    @10
    @24
    @32
    @7
    @9
    @32
    @5
    @8
    @6
    cc0
    wph
    @31
    @40
    @6
    cc0
    wne
    @41
    @6
    @47
    gt0ne0d
    3expia
    necon4d
    @32
    @7
    @9
    @36
    cc0
    wceq
    #
    wph
    @48
    @31
    @38
    adantr
    @9
    @6
    @36
    cc0
    @39
    eqeq1d
    syl5ibrcom
    impbid
    @32
    @23
    vy
    @2
    wph
    @31
    @11
    @2
    wcel
    #
    @23
    wph
    @31
    @49
    w3a
    #
    @17
    @22
    @50
    @17
    @5
    @8
    @11
    @8
    @50
    @9
    wa
    #
    @36
    cc0
    @14
    @16
    @50
    @48
    @9
    wph
    @31
    @48
    @49
    @38
    3ad2ant1
    #
    adantr
    @51
    @13
    @8
    cF
    @9
    @50
    @13
    @8
    @11
    @12
    co
    #
    @8
    @5
    @8
    @11
    @12
    oveq1
    @50
    cR
    crg
    wcel
    #
    @49
    @53
    @8
    wceq
    wph
    @31
    @54
    @49
    isabvd.1
    3ad2ant1
    #
    wph
    @31
    @49
    simp3
    #
    @2
    cR
    @12
    @11
    @8
    @2
    eqid
    #
    @12
    eqid
    #
    @8
    eqid
    #
    ringlz
    syl2anc
    sylan9eqr
    fveq2d
    @51
    @16
    cc0
    @15
    cmul
    co
    cc0
    @51
    @6
    cc0
    @15
    cmul
    @9
    @50
    @6
    @36
    cc0
    @39
    @52
    sylan9eqr
    #
    oveq1d
    @51
    @15
    @50
    @15
    cc
    wcel
    @9
    @50
    @15
    @50
    @2
    cr
    @11
    cF
    wph
    @31
    @29
    @49
    @30
    3ad2ant1
    #
    @56
    ffvelrnd
    #
    recnd
    adantr
    mul02d
    eqtrd
    3eqtr4d
    @50
    @11
    @8
    wceq
    #
    wa
    #
    @36
    cc0
    @14
    @16
    @50
    @48
    @63
    @52
    adantr
    @64
    @13
    @8
    cF
    @63
    @50
    @13
    @5
    @8
    @12
    co
    #
    @8
    @11
    @8
    @5
    @12
    oveq2
    @50
    @54
    @31
    @65
    @8
    wceq
    @55
    wph
    @31
    @49
    simp2
    #
    @2
    cR
    @12
    @5
    @8
    @57
    @58
    @59
    ringrz
    syl2anc
    sylan9eqr
    fveq2d
    @64
    @16
    @6
    cc0
    cmul
    co
    cc0
    @64
    @15
    cc0
    @6
    cmul
    @63
    @50
    @15
    @36
    cc0
    @11
    @8
    cF
    fveq2
    @52
    sylan9eqr
    #
    oveq2d
    @64
    @6
    @50
    @6
    cc
    wcel
    @63
    @50
    @6
    @50
    @2
    cr
    @5
    cF
    @61
    @66
    ffvelrnd
    #
    recnd
    adantr
    mul01d
    eqtrd
    3eqtr4d
    @50
    @40
    @11
    @8
    wne
    #
    wa
    #
    wa
    #
    @5
    @11
    c.x
    co
    #
    cF
    cfv
    #
    @14
    @16
    @71
    @72
    @13
    cF
    @71
    c.x
    @12
    @5
    @11
    @71
    wph
    c.x
    @12
    wceq
    wph
    @31
    @49
    @70
    simpl1
    #
    isabvd.t
    syl
    oveqd
    fveq2d
    @71
    wph
    @43
    @44
    @11
    cB
    wcel
    #
    @11
    c.0
    wne
    #
    @73
    @16
    wceq
    @74
    @71
    @5
    @2
    cB
    wph
    @31
    @49
    @70
    simpl2
    @71
    wph
    @45
    @74
    isabvd.b
    syl
    #
    eleqtrrd
    #
    @71
    @5
    @8
    c.0
    @50
    @40
    @69
    simprl
    @71
    wph
    @46
    @74
    isabvd.z
    syl
    #
    neeqtrrd
    #
    @71
    @11
    @2
    cB
    wph
    @31
    @49
    @70
    simpl3
    @77
    eleqtrrd
    #
    @71
    @11
    @8
    c.0
    @50
    @40
    @69
    simprr
    @79
    neeqtrrd
    #
    isabvd.5
    syl122anc
    eqtr3d
    pm2.61da2ne
    @50
    @22
    @5
    @8
    @11
    @8
    @51
    @20
    @15
    @21
    cle
    @51
    @19
    @11
    cF
    @9
    @50
    @19
    @8
    @11
    @18
    co
    #
    @11
    @5
    @8
    @11
    @18
    oveq1
    @50
    cR
    cgrp
    wcel
    #
    @49
    @83
    @11
    wceq
    @50
    @54
    @84
    @55
    cR
    ringgrp
    syl
    #
    @56
    @2
    @18
    cR
    @11
    @8
    @57
    @18
    eqid
    #
    @59
    grplid
    syl2anc
    sylan9eqr
    fveq2d
    @51
    @34
    @15
    @21
    cle
    wbr
    #
    @51
    cc0
    cc0
    @6
    cle
    0le0
    @60
    syl5breqr
    @50
    @34
    @87
    wb
    @9
    @50
    @15
    @6
    @62
    @68
    addge02d
    adantr
    mpbid
    eqbrtrd
    @64
    @20
    @6
    @21
    cle
    @64
    @19
    @5
    cF
    @63
    @50
    @19
    @5
    @8
    @18
    co
    #
    @5
    @11
    @8
    @5
    @18
    oveq2
    @50
    @84
    @31
    @88
    @5
    wceq
    @85
    @66
    @2
    @18
    cR
    @5
    @8
    @57
    @86
    @59
    grprid
    syl2anc
    sylan9eqr
    fveq2d
    @64
    cc0
    @15
    cle
    wbr
    #
    @6
    @21
    cle
    wbr
    #
    @64
    cc0
    cc0
    @15
    cle
    0le0
    @67
    syl5breqr
    @50
    @89
    @90
    wb
    @63
    @50
    @6
    @15
    @68
    @62
    addge01d
    adantr
    mpbid
    eqbrtrd
    @71
    @5
    @11
    c.pl
    co
    #
    cF
    cfv
    #
    @20
    @21
    cle
    @71
    @91
    @19
    cF
    @71
    c.pl
    @18
    @5
    @11
    @71
    wph
    c.pl
    @18
    wceq
    @74
    isabvd.p
    syl
    oveqd
    fveq2d
    @71
    wph
    @43
    @44
    @75
    @76
    @92
    @21
    cle
    wbr
    @74
    @78
    @80
    @81
    @82
    isabvd.6
    syl122anc
    eqbrtrrd
    pm2.61da2ne
    jca
    3expia
    ralrimiv
    jca
    ralrimiva
    wph
    @54
    @1
    @4
    @26
    wa
    wb
    isabvd.1
    vx
    vy
    @0
    @2
    @18
    cR
    @12
    cF
    @8
    @0
    eqid
    @57
    @86
    @58
    @59
    isabv
    syl
    mpbir2and
    isabvd.a
    eleqtrrd
end
