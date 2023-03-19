include "wa.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "cdv.mm"
include "cc.mm"
include "wf.mm"
include "adantr.mm"
include "ffvelrnd.mm"
include "subcld.mm"
include "cdm.mm"
include "wceq.mm"
include "cmap.mm"
include "wcel.mm"
include "cv.mm"
include "cmpt.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "wfn.mm"
include "culm.mm"
include "wbr.mm"
include "cvv.mm"
include "wral.mm"
include "rgenw.mm"
include "fnmpt.mm"
include "mp1i.mm"
include "ulmf2.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "elmapi.mm"
include "fdm.mm"
include "dvbsss.mm"
include "syl6eqssr.mm"
include "wss.mm"
include "cr.mm"
include "cpr.mm"
include "recnprss.mm"
include "sstrd.mm"
include "sseldd.mm"
include "subne0d.mm"
include "divcld.mm"
include "ulmcl.mm"
include "rpred.mm"
include "cabs.mm"
include "caddc.mm"
include "c2.mm"
include "abscld.mm"
include "readdcld.mm"
include "rehalfcld.mm"
include "abs3difd.mm"
include "clt.mm"
include "cle.mm"
include "sub4d.mm"
include "oveq1d.mm"
include "divsubdird.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "absdivd.mm"
include "eqtr3d.mm"
include "cmul.mm"
include "csn.mm"
include "cxp.mm"
include "cuz.mm"
include "cz.mm"
include "syl6eleq.mm"
include "eluzelz.mm"
include "cli.mm"
include "ralrimiva.mm"
include "mpteq2dv.mm"
include "breq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "a1i.mm"
include "weq.mm"
include "fveq1d.mm"
include "adantl.mm"
include "ffvelrnda.mm"
include "eqeltrd.mm"
include "eqtr4d.mm"
include "climsubc1.mm"
include "oveq12d.mm"
include "climsub.mm"
include "climabs.mm"
include "remulcld.mm"
include "recnd.mm"
include "eqimss2i.mm"
include "climconst2.mm"
include "uztrn2.mm"
include "sylan.mm"
include "syldan.mm"
include "fvconst2.mm"
include "cof.mm"
include "ffn.mm"
include "ulmscl.mm"
include "ad2antrr.mm"
include "fnfvof.mm"
include "syl22anc.mm"
include "ccom.mm"
include "cres.mm"
include "cbl.mm"
include "ovresd.mm"
include "cnmetdval.mm"
include "eqbrtrd.mm"
include "cxmt.mm"
include "cxr.mm"
include "wb.mm"
include "cnxmet.mm"
include "xmetres2.mm"
include "sylancr.mm"
include "rpxrd.mm"
include "elbl3.mm"
include "mpbird.mm"
include "crp.mm"
include "blcntr.mm"
include "syl3anc.mm"
include "jca.mm"
include "fmptd.mm"
include "fvexd.mm"
include "feqmptd.mm"
include "offval2.mm"
include "feq1d.mm"
include "dvmptsub.mm"
include "dmeqd.mm"
include "dmmpti.mm"
include "syl6eq.mm"
include "sseqtr4d.mm"
include "sselda.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "sylan9eq.mm"
include "dvmptcl.mm"
include "abssubd.mm"
include "breq1d.mm"
include "ralbidv.mm"
include "rspccva.mm"
include "ltled.mm"
include "dvlip2.mm"
include "mpdan.mm"
include "eqbrtrrd.mm"
include "3brtr4d.mm"
include "climle.mm"
include "absrpcld.mm"
include "ledivmul2d.mm"
include "lttrd.mm"
include "mpd.mm"
include "leltaddd.mm"
include "2halvesd.mm"
include "breqtrd.mm"
include "lelttrd.mm"
include "abs3lemd.mm"

theorem ulmdvlem1
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vz: setvar z
  let cC: class C
  let cR: class R
  let cS: class S
  let cU: class U
  let vk: setvar k
  let vm: setvar m
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vj: setvar j
  let vn: setvar n
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vr: setvar r
  assume ulmdv.z: |- Z = ( ZZ>= ` M )
  assume ulmdv.s: |- ( ph -> S e. { RR , CC } )
  assume ulmdv.m: |- ( ph -> M e. ZZ )
  assume ulmdv.f: |- ( ph -> F : Z --> ( CC ^m X ) )
  assume ulmdv.g: |- ( ph -> G : X --> CC )
  assume ulmdv.l: |- ( ( ph /\ z e. X ) -> ( k e. Z |-> ( ( F ` k ) ` z ) ) ~~> ( G ` z ) )
  assume ulmdv.u: |- ( ph -> ( k e. Z |-> ( S _D ( F ` k ) ) ) ( ~~>u ` X ) H )
  assume ulmdvlem1.c: |- ( ( ph /\ ps ) -> C e. X )
  assume ulmdvlem1.r: |- ( ( ph /\ ps ) -> R e. RR+ )
  assume ulmdvlem1.u: |- ( ( ph /\ ps ) -> U e. RR+ )
  assume ulmdvlem1.v: |- ( ( ph /\ ps ) -> W e. RR+ )
  assume ulmdvlem1.l: |- ( ( ph /\ ps ) -> U < W )
  assume ulmdvlem1.b: |- ( ( ph /\ ps ) -> ( C ( ball ` ( ( abs o. - ) |` ( S X. S ) ) ) U ) C_ X )
  assume ulmdvlem1.a: |- ( ( ph /\ ps ) -> ( abs ` ( Y - C ) ) < U )
  assume ulmdvlem1.n: |- ( ( ph /\ ps ) -> N e. Z )
  assume ulmdvlem1.1: |- ( ( ph /\ ps ) -> A. m e. ( ZZ>= ` N ) A. x e. X ( abs ` ( ( ( S _D ( F ` N ) ) ` x ) - ( ( S _D ( F ` m ) ) ` x ) ) ) < ( ( R / 2 ) / 2 ) )
  assume ulmdvlem1.2: |- ( ( ph /\ ps ) -> ( abs ` ( ( ( S _D ( F ` N ) ) ` C ) - ( H ` C ) ) ) < ( R / 2 ) )
  assume ulmdvlem1.y: |- ( ( ph /\ ps ) -> Y e. X )
  assume ulmdvlem1.3: |- ( ( ph /\ ps ) -> Y =/= C )
  assume ulmdvlem1.4: |- ( ( ph /\ ps ) -> ( ( abs ` ( Y - C ) ) < W -> ( abs ` ( ( ( ( ( F ` N ) ` Y ) - ( ( F ` N ) ` C ) ) / ( Y - C ) ) - ( ( S _D ( F ` N ) ) ` C ) ) ) < ( ( R / 2 ) / 2 ) ) )

  disjoint k m
  disjoint k x
  disjoint k z
  disjoint F k
  disjoint m x
  disjoint m z
  disjoint F m
  disjoint x z
  disjoint F x
  disjoint F z
  disjoint G z
  disjoint N k
  disjoint N m
  disjoint N x
  disjoint C k
  disjoint C z
  disjoint H z
  disjoint M k
  disjoint M x
  disjoint k ph
  disjoint m ph
  disjoint ph x
  disjoint ph z
  disjoint S k
  disjoint S m
  disjoint S x
  disjoint S z
  disjoint R m
  disjoint R x
  disjoint X k
  disjoint X m
  disjoint X x
  disjoint X z
  disjoint Y k
  disjoint Y z
  disjoint Z k
  disjoint Z m
  disjoint Z x
  disjoint Z z
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j s
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint k n
  disjoint k s
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k y
  disjoint m n
  disjoint m s
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m y
  disjoint n s
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint F s
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint y z
  disjoint F y
  disjoint n r
  disjoint G n
  disjoint r s
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r y
  disjoint r z
  disjoint G r
  disjoint G s
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G y
  disjoint N n
  disjoint N w
  disjoint N y
  disjoint C n
  disjoint C y
  disjoint j r
  disjoint H j
  disjoint H n
  disjoint H r
  disjoint H s
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint H y
  disjoint M j
  disjoint M n
  disjoint n ps
  disjoint ps w
  disjoint ps y
  disjoint j ph
  disjoint k r
  disjoint m r
  disjoint n ph
  disjoint r x
  disjoint ph r
  disjoint ph s
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint S j
  disjoint S n
  disjoint S s
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S y
  disjoint U y
  disjoint R n
  disjoint R y
  disjoint X j
  disjoint X n
  disjoint X r
  disjoint X s
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X y
  disjoint Y n
  disjoint Y y
  disjoint Z j
  disjoint Z n
  disjoint Z s
  disjoint Z u
  disjoint Z v
  disjoint Z w
  disjoint Z y
  assert |- ( ( ph /\ ps ) -> ( abs ` ( ( ( ( G ` Y ) - ( G ` C ) ) / ( Y - C ) ) - ( H ` C ) ) ) < R )

  proof
    wph
    wps
    wa
    #
    cY
    cG
    cfv
    #
    cC
    cG
    cfv
    #
    cmin
    co
    #
    cY
    cC
    cmin
    co
    #
    cdiv
    co
    #
    cC
    cH
    cfv
    cC
    cS
    cN
    cF
    cfv
    #
    cdv
    co
    #
    cfv
    #
    cR
    @0
    @3
    @4
    @0
    @1
    @2
    @0
    cX
    cc
    cY
    cG
    wph
    cX
    cc
    cG
    wf
    wps
    ulmdv.g
    adantr
    #
    ulmdvlem1.y
    ffvelrnd
    #
    @0
    cX
    cc
    cC
    cG
    @9
    ulmdvlem1.c
    ffvelrnd
    #
    subcld
    #
    @0
    cY
    cC
    @0
    cX
    cc
    cY
    @0
    cX
    cS
    cc
    @0
    cX
    @7
    cdm
    #
    cS
    @0
    cX
    cc
    @7
    wf
    #
    @13
    cX
    wceq
    @0
    @7
    cc
    cX
    cmap
    co
    #
    wcel
    @14
    @0
    cN
    vk
    cZ
    cS
    vk
    cv
    #
    cF
    cfv
    #
    cdv
    co
    #
    cmpt
    #
    cfv
    #
    @7
    @15
    @0
    cN
    cZ
    wcel
    #
    @20
    @7
    wceq
    ulmdvlem1.n
    vk
    cN
    @18
    @7
    cZ
    @19
    @16
    cN
    wceq
    @17
    @6
    cS
    cdv
    @16
    cN
    cF
    fveq2
    oveq2d
    @19
    eqid
    #
    cS
    @6
    cdv
    ovex
    fvmpt
    syl
    @0
    cZ
    @15
    cN
    @19
    wph
    cZ
    @15
    @19
    wf
    #
    wps
    wph
    @19
    cZ
    wfn
    #
    @19
    cH
    cX
    culm
    cfv
    wbr
    #
    @23
    @18
    cvv
    wcel
    #
    vk
    cZ
    wral
    @24
    wph
    @26
    vk
    cZ
    cS
    @17
    cdv
    ovex
    rgenw
    vk
    cZ
    @18
    @19
    cvv
    @22
    fnmpt
    mp1i
    ulmdv.u
    cX
    @19
    cH
    cZ
    ulmf2
    syl2anc
    #
    adantr
    ulmdvlem1.n
    ffvelrnd
    eqeltrrd
    @7
    cc
    cX
    elmapi
    syl
    #
    cX
    cc
    @7
    fdm
    syl
    cS
    @6
    dvbsss
    syl6eqssr
    #
    wph
    cS
    cc
    wss
    #
    wps
    wph
    cS
    cr
    cc
    cpr
    wcel
    #
    @30
    ulmdv.s
    cS
    recnprss
    syl
    adantr
    #
    sstrd
    #
    ulmdvlem1.y
    sseldd
    #
    @0
    cX
    cc
    cC
    @33
    ulmdvlem1.c
    sseldd
    #
    subcld
    #
    @0
    cY
    cC
    @34
    @35
    ulmdvlem1.3
    subne0d
    #
    divcld
    #
    @0
    cX
    cc
    cC
    cH
    wph
    cX
    cc
    cH
    wf
    #
    wps
    wph
    @25
    @39
    ulmdv.u
    cX
    @19
    cH
    ulmcl
    syl
    adantr
    ulmdvlem1.c
    ffvelrnd
    @0
    cX
    cc
    cC
    @7
    @28
    ulmdvlem1.c
    ffvelrnd
    #
    @0
    cR
    ulmdvlem1.r
    rpred
    #
    @0
    @5
    @8
    cmin
    co
    #
    cabs
    cfv
    @5
    cY
    @6
    cfv
    #
    cC
    @6
    cfv
    #
    cmin
    co
    #
    @4
    cdiv
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @46
    @8
    cmin
    co
    #
    cabs
    cfv
    #
    caddc
    co
    #
    cR
    c2
    cdiv
    co
    #
    @0
    @42
    @0
    @5
    @8
    @38
    @40
    subcld
    abscld
    @0
    @48
    @50
    @0
    @47
    @0
    @5
    @46
    @38
    @0
    @45
    @4
    @0
    @43
    @44
    @0
    cX
    cc
    cY
    @6
    @0
    @6
    @15
    wcel
    cX
    cc
    @6
    wf
    #
    @0
    cZ
    @15
    cN
    cF
    wph
    cZ
    @15
    cF
    wf
    wps
    ulmdv.f
    adantr
    #
    ulmdvlem1.n
    ffvelrnd
    @6
    cc
    cX
    elmapi
    syl
    #
    ulmdvlem1.y
    ffvelrnd
    #
    @0
    cX
    cc
    cC
    @6
    @55
    ulmdvlem1.c
    ffvelrnd
    #
    subcld
    #
    @36
    @37
    divcld
    #
    subcld
    abscld
    #
    @0
    @49
    @0
    @46
    @8
    @59
    @40
    subcld
    abscld
    #
    readdcld
    @0
    cR
    @41
    rehalfcld
    #
    @0
    @5
    @8
    @46
    @38
    @40
    @59
    abs3difd
    @0
    @51
    @52
    c2
    cdiv
    co
    #
    @63
    caddc
    co
    @52
    clt
    @0
    @48
    @50
    @63
    @63
    @60
    @61
    @0
    @52
    @62
    rehalfcld
    #
    @64
    @0
    @48
    @1
    @43
    cmin
    co
    #
    @2
    @44
    cmin
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @4
    cabs
    cfv
    #
    cdiv
    co
    #
    @63
    cle
    @0
    @67
    @4
    cdiv
    co
    #
    cabs
    cfv
    @48
    @70
    @0
    @71
    @47
    cabs
    @0
    @71
    @3
    @45
    cmin
    co
    #
    @4
    cdiv
    co
    @47
    @0
    @67
    @72
    @4
    cdiv
    @0
    @1
    @43
    @2
    @44
    @10
    @56
    @11
    @57
    sub4d
    oveq1d
    @0
    @3
    @45
    @4
    @12
    @58
    @36
    @37
    divsubdird
    eqtrd
    fveq2d
    @0
    @67
    @4
    @0
    @65
    @66
    @0
    @1
    @43
    @10
    @56
    subcld
    @0
    @2
    @44
    @11
    @57
    subcld
    subcld
    #
    @36
    @37
    absdivd
    eqtr3d
    @0
    @70
    @63
    cle
    wbr
    @68
    @63
    @69
    cmul
    co
    #
    cle
    wbr
    @0
    @68
    @74
    vn
    vk
    cZ
    cY
    @17
    cfv
    #
    @43
    cmin
    co
    #
    cC
    @17
    cfv
    #
    @44
    cmin
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cmpt
    #
    cZ
    @74
    csn
    cxp
    #
    cN
    cN
    cuz
    cfv
    #
    @83
    eqid
    @0
    cN
    cM
    cuz
    cfv
    #
    wcel
    cN
    cz
    wcel
    @0
    cN
    cZ
    @84
    ulmdvlem1.n
    ulmdv.z
    syl6eleq
    cM
    cN
    eluzelz
    syl
    @0
    @67
    vn
    vk
    cZ
    @79
    cmpt
    #
    @81
    cM
    cvv
    cZ
    ulmdv.z
    @0
    @65
    @66
    vn
    vk
    cZ
    @76
    cmpt
    #
    vk
    cZ
    @78
    cmpt
    #
    @85
    cM
    cvv
    cZ
    ulmdv.z
    wph
    cM
    cz
    wcel
    #
    wps
    ulmdv.m
    adantr
    #
    @0
    @1
    @43
    vn
    vk
    cZ
    @75
    cmpt
    #
    @86
    cM
    cvv
    cZ
    ulmdv.z
    @89
    @0
    cY
    cX
    wcel
    #
    vk
    cZ
    vz
    cv
    #
    @17
    cfv
    #
    cmpt
    #
    @92
    cG
    cfv
    #
    cli
    wbr
    #
    vz
    cX
    wral
    #
    @90
    @1
    cli
    wbr
    #
    ulmdvlem1.y
    wph
    @97
    wps
    wph
    @96
    vz
    cX
    ulmdv.l
    ralrimiva
    adantr
    #
    @96
    @98
    vz
    cY
    cX
    @92
    cY
    wceq
    #
    @94
    @90
    @95
    @1
    cli
    @100
    vk
    cZ
    @93
    @75
    @92
    cY
    @17
    fveq2
    mpteq2dv
    @92
    cY
    cG
    fveq2
    breq12d
    rspcv
    sylc
    @56
    @86
    cvv
    wcel
    @0
    vk
    cZ
    @76
    cZ
    @84
    cvv
    ulmdv.z
    cM
    cuz
    fvex
    eqeltri
    #
    mptex
    a1i
    @0
    vn
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @102
    @90
    cfv
    #
    cY
    @102
    cF
    cfv
    #
    cfv
    #
    cc
    @103
    @105
    @107
    wceq
    @0
    vk
    @102
    @75
    @107
    cZ
    @90
    vk
    vn
    weq
    #
    cY
    @17
    @106
    @16
    @102
    cF
    fveq2
    #
    fveq1d
    #
    @90
    eqid
    cY
    @106
    fvex
    fvmpt
    adantl
    #
    @104
    cX
    cc
    cY
    @106
    @104
    @106
    @15
    wcel
    cX
    cc
    @106
    wf
    #
    @0
    cZ
    @15
    @102
    cF
    @54
    ffvelrnda
    @106
    cc
    cX
    elmapi
    syl
    #
    @0
    @91
    @103
    ulmdvlem1.y
    adantr
    ffvelrnd
    #
    eqeltrd
    @104
    @102
    @86
    cfv
    #
    @107
    @43
    cmin
    co
    #
    @105
    @43
    cmin
    co
    @103
    @115
    @116
    wceq
    @0
    vk
    @102
    @76
    @116
    cZ
    @86
    @108
    @75
    @107
    @43
    cmin
    @110
    oveq1d
    #
    @86
    eqid
    @107
    @43
    cmin
    ovex
    fvmpt
    adantl
    #
    @104
    @105
    @107
    @43
    cmin
    @111
    oveq1d
    eqtr4d
    climsubc1
    @85
    cvv
    wcel
    @0
    vk
    cZ
    @79
    @101
    mptex
    a1i
    @0
    @2
    @44
    vn
    vk
    cZ
    @77
    cmpt
    #
    @87
    cM
    cvv
    cZ
    ulmdv.z
    @89
    @0
    cC
    cX
    wcel
    #
    @97
    @119
    @2
    cli
    wbr
    #
    ulmdvlem1.c
    @99
    @96
    @121
    vz
    cC
    cX
    @92
    cC
    wceq
    #
    @94
    @119
    @95
    @2
    cli
    @122
    vk
    cZ
    @93
    @77
    @92
    cC
    @17
    fveq2
    mpteq2dv
    @92
    cC
    cG
    fveq2
    breq12d
    rspcv
    sylc
    @57
    @87
    cvv
    wcel
    @0
    vk
    cZ
    @78
    @101
    mptex
    a1i
    @104
    @102
    @119
    cfv
    #
    cC
    @106
    cfv
    #
    cc
    @103
    @123
    @124
    wceq
    @0
    vk
    @102
    @77
    @124
    cZ
    @119
    @108
    cC
    @17
    @106
    @109
    fveq1d
    #
    @119
    eqid
    cC
    @106
    fvex
    fvmpt
    adantl
    #
    @104
    cX
    cc
    cC
    @106
    @113
    @0
    @120
    @103
    ulmdvlem1.c
    adantr
    ffvelrnd
    #
    eqeltrd
    @104
    @102
    @87
    cfv
    #
    @124
    @44
    cmin
    co
    #
    @123
    @44
    cmin
    co
    @103
    @128
    @129
    wceq
    @0
    vk
    @102
    @78
    @129
    cZ
    @87
    @108
    @77
    @124
    @44
    cmin
    @125
    oveq1d
    #
    @87
    eqid
    @124
    @44
    cmin
    ovex
    fvmpt
    adantl
    #
    @104
    @123
    @124
    @44
    cmin
    @126
    oveq1d
    eqtr4d
    climsubc1
    @104
    @115
    @116
    cc
    @118
    @104
    @107
    @43
    @114
    @0
    @43
    cc
    wcel
    @103
    @56
    adantr
    subcld
    #
    eqeltrd
    @104
    @128
    @129
    cc
    @131
    @104
    @124
    @44
    @127
    @0
    @44
    cc
    wcel
    @103
    @57
    adantr
    subcld
    #
    eqeltrd
    @104
    @102
    @85
    cfv
    #
    @116
    @129
    cmin
    co
    #
    @115
    @128
    cmin
    co
    @103
    @134
    @135
    wceq
    @0
    vk
    @102
    @79
    @135
    cZ
    @85
    @108
    @76
    @116
    @78
    @129
    cmin
    @117
    @130
    oveq12d
    #
    @85
    eqid
    @116
    @129
    cmin
    ovex
    fvmpt
    adantl
    #
    @104
    @115
    @116
    @128
    @129
    cmin
    @118
    @131
    oveq12d
    eqtr4d
    climsub
    @81
    cvv
    wcel
    @0
    vk
    cZ
    @80
    @101
    mptex
    a1i
    @89
    @104
    @134
    @135
    cc
    @137
    @104
    @116
    @129
    @132
    @133
    subcld
    #
    eqeltrd
    @104
    @102
    @81
    cfv
    #
    @135
    cabs
    cfv
    #
    @134
    cabs
    cfv
    @103
    @139
    @140
    wceq
    #
    @0
    vk
    @102
    @80
    @140
    cZ
    @81
    @108
    @79
    @135
    cabs
    @136
    fveq2d
    @81
    eqid
    @135
    cabs
    fvex
    fvmpt
    #
    adantl
    @104
    @134
    @135
    cabs
    @137
    fveq2d
    eqtr4d
    climabs
    @0
    @74
    cc
    wcel
    @88
    @82
    @74
    cli
    wbr
    @0
    @74
    @0
    @63
    @69
    @64
    @0
    @4
    @36
    abscld
    #
    remulcld
    #
    recnd
    @89
    @74
    cM
    cZ
    cZ
    @84
    ulmdv.z
    eqimss2i
    @101
    climconst2
    syl2anc
    @0
    @102
    @83
    wcel
    #
    wa
    #
    @139
    @140
    cr
    @146
    @103
    @141
    @0
    @21
    @145
    @103
    ulmdvlem1.n
    cM
    @102
    cN
    cZ
    ulmdv.z
    uztrn2
    sylan
    #
    @142
    syl
    #
    @0
    @145
    @103
    @140
    cr
    wcel
    @147
    @104
    @135
    @138
    abscld
    syldan
    eqeltrd
    @146
    @102
    @82
    cfv
    #
    @74
    cr
    @146
    @103
    @149
    @74
    wceq
    @147
    cZ
    @74
    @102
    @63
    @69
    cmul
    ovex
    fvconst2
    syl
    #
    @0
    @74
    cr
    wcel
    @145
    @144
    adantr
    eqeltrd
    @146
    @140
    @74
    @139
    @149
    cle
    @146
    cY
    @106
    @6
    cmin
    cof
    co
    #
    cfv
    #
    cC
    @151
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @140
    @74
    cle
    @146
    @154
    @135
    cabs
    @146
    @152
    @116
    @153
    @129
    cmin
    @146
    @106
    cX
    wfn
    #
    @6
    cX
    wfn
    #
    cX
    cvv
    wcel
    #
    @91
    @152
    @116
    wceq
    @146
    @112
    @156
    @0
    @145
    @103
    @112
    @147
    @113
    syldan
    #
    cX
    cc
    @106
    ffn
    syl
    #
    @146
    @53
    @157
    @0
    @53
    @145
    @55
    adantr
    #
    cX
    cc
    @6
    ffn
    syl
    #
    wph
    @158
    wps
    @145
    wph
    @25
    @158
    ulmdv.u
    cX
    @19
    cH
    ulmscl
    syl
    ad2antrr
    #
    @0
    @91
    @145
    ulmdvlem1.y
    adantr
    cX
    cmin
    @106
    @6
    cvv
    cY
    fnfvof
    syl22anc
    @146
    @156
    @157
    @158
    @120
    @153
    @129
    wceq
    @160
    @162
    @163
    @0
    @120
    @145
    ulmdvlem1.c
    adantr
    cX
    cmin
    @106
    @6
    cvv
    cC
    fnfvof
    syl22anc
    oveq12d
    fveq2d
    @146
    cY
    cC
    cU
    cabs
    cmin
    ccom
    #
    cS
    cS
    cxp
    cres
    #
    cbl
    cfv
    co
    #
    wcel
    #
    cC
    @166
    wcel
    #
    wa
    @155
    @74
    cle
    wbr
    @146
    @167
    @168
    @0
    @167
    @145
    @0
    @167
    cY
    cC
    @165
    co
    #
    cU
    clt
    wbr
    #
    @0
    @169
    @69
    cU
    clt
    @0
    @169
    cY
    cC
    @164
    co
    #
    @69
    @0
    cY
    cC
    @164
    cS
    @0
    cX
    cS
    cY
    @29
    ulmdvlem1.y
    sseldd
    #
    @0
    cX
    cS
    cC
    @29
    ulmdvlem1.c
    sseldd
    #
    ovresd
    @0
    cY
    cc
    wcel
    cC
    cc
    wcel
    @171
    @69
    wceq
    @34
    @35
    cY
    cC
    @164
    @164
    eqid
    cnmetdval
    syl2anc
    eqtrd
    ulmdvlem1.a
    eqbrtrd
    @0
    @165
    cS
    cxmt
    cfv
    wcel
    #
    cU
    cxr
    wcel
    #
    cC
    cS
    wcel
    #
    cY
    cS
    wcel
    @167
    @170
    wb
    @0
    @164
    cc
    cxmt
    cfv
    wcel
    @30
    @174
    cnxmet
    @32
    @164
    cS
    cc
    xmetres2
    sylancr
    #
    @0
    cU
    ulmdvlem1.u
    rpxrd
    #
    @173
    @172
    cY
    @165
    cC
    cU
    cS
    elbl3
    syl22anc
    mpbird
    adantr
    @0
    @168
    @145
    @0
    @174
    @176
    cU
    crp
    wcel
    @168
    @177
    @173
    ulmdvlem1.u
    @165
    cC
    cU
    cS
    blcntr
    syl3anc
    adantr
    jca
    @146
    vy
    cC
    @166
    cU
    cS
    @151
    @165
    @63
    cX
    cY
    cC
    wph
    @31
    wps
    @145
    ulmdv.s
    ad2antrr
    #
    @165
    eqid
    @0
    cX
    cS
    wss
    @145
    @29
    adantr
    @146
    cX
    cc
    @151
    wf
    cX
    cc
    vy
    cX
    vy
    cv
    #
    @106
    cfv
    #
    @180
    @6
    cfv
    #
    cmin
    co
    #
    cmpt
    #
    wf
    @146
    vy
    cX
    @183
    cc
    @184
    @146
    @180
    cX
    wcel
    #
    wa
    #
    @181
    @182
    @146
    cX
    cc
    @180
    @106
    @159
    ffvelrnda
    #
    @146
    cX
    cc
    @180
    @6
    @161
    ffvelrnda
    #
    subcld
    #
    @184
    eqid
    fmptd
    @146
    cX
    cc
    @151
    @184
    @146
    vy
    cX
    @181
    @182
    cmin
    @106
    @6
    cvv
    cvv
    cvv
    @163
    @186
    @180
    @106
    fvexd
    @186
    @180
    @6
    fvexd
    @146
    vy
    cX
    cc
    @106
    @159
    feqmptd
    #
    @146
    vy
    cX
    cc
    @6
    @161
    feqmptd
    #
    offval2
    #
    feq1d
    mpbird
    @0
    @176
    @145
    @173
    adantr
    @0
    @175
    @145
    @178
    adantr
    @166
    eqid
    @146
    @166
    cX
    cS
    @151
    cdv
    co
    #
    cdm
    #
    @0
    @166
    cX
    wss
    @145
    ulmdvlem1.b
    adantr
    #
    @146
    @194
    vy
    cX
    @180
    cS
    @106
    cdv
    co
    #
    cfv
    #
    @180
    @7
    cfv
    #
    cmin
    co
    #
    cmpt
    #
    cdm
    cX
    @146
    @193
    @200
    @146
    @193
    cS
    @184
    cdv
    co
    @200
    @146
    @151
    @184
    cS
    cdv
    @192
    oveq2d
    @146
    vy
    @181
    @197
    @182
    @198
    cS
    cvv
    cvv
    cX
    @179
    @187
    @186
    @180
    @196
    fvexd
    @146
    @196
    cS
    vy
    cX
    @181
    cmpt
    #
    cdv
    co
    vy
    cX
    @197
    cmpt
    @146
    @106
    @201
    cS
    cdv
    @190
    oveq2d
    @146
    vy
    cX
    cc
    @196
    @146
    @196
    @15
    wcel
    cX
    cc
    @196
    wf
    @146
    @102
    @19
    cfv
    #
    @196
    @15
    @146
    @103
    @202
    @196
    wceq
    @147
    vk
    @102
    @18
    @196
    cZ
    @19
    @108
    @17
    @106
    cS
    cdv
    @109
    oveq2d
    @22
    cS
    @106
    cdv
    ovex
    fvmpt
    syl
    @146
    cZ
    @15
    @102
    @19
    wph
    @23
    wps
    @145
    @27
    ad2antrr
    @147
    ffvelrnd
    eqeltrrd
    @196
    cc
    cX
    elmapi
    syl
    #
    feqmptd
    eqtr3d
    @188
    @186
    @180
    @7
    fvexd
    @146
    @7
    cS
    vy
    cX
    @182
    cmpt
    #
    cdv
    co
    vy
    cX
    @198
    cmpt
    @146
    @6
    @204
    cS
    cdv
    @191
    oveq2d
    @146
    vy
    cX
    cc
    @7
    @0
    @14
    @145
    @28
    adantr
    #
    feqmptd
    eqtr3d
    dvmptsub
    #
    eqtrd
    #
    dmeqd
    vy
    cX
    @199
    @200
    @197
    @198
    cmin
    ovex
    #
    @200
    eqid
    #
    dmmpti
    syl6eq
    sseqtr4d
    @0
    @63
    cr
    wcel
    #
    @145
    @64
    adantr
    @146
    @180
    @166
    wcel
    @185
    @180
    @193
    cfv
    #
    cabs
    cfv
    #
    @63
    cle
    wbr
    @146
    @166
    cX
    @180
    @195
    sselda
    @186
    @212
    @199
    cabs
    cfv
    #
    @63
    cle
    @186
    @211
    @199
    cabs
    @146
    @185
    @211
    @180
    @200
    cfv
    #
    @199
    @146
    @180
    @193
    @200
    @207
    fveq1d
    @185
    @199
    cvv
    wcel
    #
    @214
    @199
    wceq
    @208
    vy
    cX
    @199
    cvv
    @200
    @209
    fvmpt2
    mpan2
    sylan9eq
    fveq2d
    @186
    @213
    @63
    @186
    @199
    @146
    vy
    @183
    @199
    cS
    cvv
    cX
    @179
    @189
    @215
    @186
    @208
    a1i
    @206
    dvmptcl
    abscld
    @0
    @210
    @145
    @185
    @64
    ad2antrr
    @186
    @213
    @198
    @197
    cmin
    co
    #
    cabs
    cfv
    #
    @63
    clt
    @186
    @197
    @198
    @146
    cX
    cc
    @180
    @196
    @203
    ffvelrnda
    @146
    cX
    cc
    @180
    @7
    @205
    ffvelrnda
    abssubd
    @146
    vx
    cv
    #
    @7
    cfv
    #
    @218
    @196
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @63
    clt
    wbr
    #
    vx
    cX
    wral
    #
    @185
    @217
    @63
    clt
    wbr
    #
    @0
    @219
    @218
    cS
    vm
    cv
    #
    cF
    cfv
    #
    cdv
    co
    #
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @63
    clt
    wbr
    #
    vx
    cX
    wral
    #
    vm
    @83
    wral
    @145
    @224
    ulmdvlem1.1
    @233
    @224
    vm
    @102
    @83
    vm
    vn
    weq
    #
    @232
    @223
    vx
    cX
    @234
    @231
    @222
    @63
    clt
    @234
    @230
    @221
    cabs
    @234
    @229
    @220
    @219
    cmin
    @234
    @218
    @228
    @196
    @234
    @227
    @106
    cS
    cdv
    @226
    @102
    cF
    fveq2
    oveq2d
    fveq1d
    oveq2d
    fveq2d
    breq1d
    ralbidv
    rspccva
    sylan
    @223
    @225
    vx
    @180
    cX
    vx
    vy
    weq
    #
    @222
    @217
    @63
    clt
    @235
    @221
    @216
    cabs
    @235
    @219
    @198
    @220
    @197
    cmin
    @218
    @180
    @7
    fveq2
    @218
    @180
    @196
    fveq2
    oveq12d
    fveq2d
    breq1d
    rspccva
    sylan
    eqbrtrd
    ltled
    eqbrtrd
    syldan
    dvlip2
    mpdan
    eqbrtrrd
    @148
    @150
    3brtr4d
    climle
    @0
    @68
    @63
    @69
    @0
    @67
    @73
    abscld
    @64
    @0
    @4
    @36
    @37
    absrpcld
    ledivmul2d
    mpbird
    eqbrtrd
    @0
    @69
    cW
    clt
    wbr
    @50
    @63
    clt
    wbr
    @0
    @69
    cU
    cW
    @143
    @0
    cU
    ulmdvlem1.u
    rpred
    @0
    cW
    ulmdvlem1.v
    rpred
    ulmdvlem1.a
    ulmdvlem1.l
    lttrd
    ulmdvlem1.4
    mpd
    leltaddd
    @0
    @52
    @0
    @52
    @62
    recnd
    2halvesd
    breqtrd
    lelttrd
    ulmdvlem1.2
    abs3lemd
end
