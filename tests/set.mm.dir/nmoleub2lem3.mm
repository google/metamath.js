include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cdiv.mm"
include "cv.mm"
include "clt.mm"
include "wa.mm"
include "cq.mm"
include "wcel.mm"
include "simprl.mm"
include "cr.mm"
include "qre.mm"
include "ad2antlr.mm"
include "rpred.mm"
include "remulcld.mm"
include "cngp.mm"
include "cbs.mm"
include "cnlm.mm"
include "cclm.mm"
include "elin1d.mm"
include "nlmngp.mm"
include "syl.mm"
include "clmhm.mm"
include "wf.mm"
include "eqid.mm"
include "lmhmf.mm"
include "ffvelrnd.mm"
include "nmcl.mm"
include "syl2anc.mm"
include "cc0.mm"
include "0red.mm"
include "nmge0.mm"
include "mulge0d.mm"
include "wn.mm"
include "ltnled.mm"
include "mpbird.mm"
include "lelttrd.mm"
include "elrpd.mm"
include "rerpdivcld.mm"
include "ad2antrr.mm"
include "cvsca.mm"
include "csca.mm"
include "cnm.mm"
include "wceq.mm"
include "sselda.mm"
include "adantr.mm"
include "lmhmlin.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "lmhmsca.mm"
include "syl6eqr.mm"
include "eleqtrrd.mm"
include "nmvs.mm"
include "fveq1d.mm"
include "cabs.mm"
include "elin2d.mm"
include "clmabs.mm"
include "rpge0d.mm"
include "divge0.mm"
include "syl22anc.mm"
include "ltled.mm"
include "absidd.mm"
include "eqtr3d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "3eqtrd.mm"
include "clmvscl.mm"
include "simprr.mm"
include "wb.mm"
include "c0g.mm"
include "wne.mm"
include "crp.mm"
include "nmrpcl.mm"
include "rpregt0d.mm"
include "ltmuldiv.mm"
include "eqbrtrd.mm"
include "wi.mm"
include "mp2d.mm"
include "eqbrtrrd.mm"
include "ledivmul2d.mm"
include "mpbid.mm"
include "jca.mm"
include "lemuldiv.mm"
include "lensymd.mm"
include "pm2.21dd.mm"
include "wrex.mm"
include "cc.mm"
include "recnd.mm"
include "w3a.mm"
include "mulass.mm"
include "mul12.mm"
include "ltmul2dd.mm"
include "lt2mul2div.mm"
include "qbtwnre.mm"
include "r19.29a.mm"
include "pm2.65i.mm"

theorem nmoleub2lem3
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cO: class O
  let wps: wff ps
  assume nmoleub2.n: |- N = ( S normOp T )
  assume nmoleub2.v: |- V = ( Base ` S )
  assume nmoleub2.l: |- L = ( norm ` S )
  assume nmoleub2.m: |- M = ( norm ` T )
  assume nmoleub2.g: |- G = ( Scalar ` S )
  assume nmoleub2.w: |- K = ( Base ` G )
  assume nmoleub2.s: |- ( ph -> S e. ( NrmMod i^i CMod ) )
  assume nmoleub2.t: |- ( ph -> T e. ( NrmMod i^i CMod ) )
  assume nmoleub2.f: |- ( ph -> F e. ( S LMHom T ) )
  assume nmoleub2.a: |- ( ph -> A e. RR* )
  assume nmoleub2.r: |- ( ph -> R e. RR+ )
  assume nmoleub2a.5: |- ( ph -> QQ C_ K )
  assume nmoleub2lem3.p: |- .x. = ( .s ` S )
  assume nmoleub2lem3.1: |- ( ph -> A e. RR )
  assume nmoleub2lem3.2: |- ( ph -> 0 <_ A )
  assume nmoleub2lem3.3: |- ( ph -> B e. V )
  assume nmoleub2lem3.4: |- ( ph -> B =/= ( 0g ` S ) )
  assume nmoleub2lem3.5: |- ( ph -> ( ( r .x. B ) e. V -> ( ( L ` ( r .x. B ) ) < R -> ( ( M ` ( F ` ( r .x. B ) ) ) / R ) <_ A ) ) )
  assume nmoleub2lem3.6: |- ( ph -> -. ( M ` ( F ` B ) ) <_ ( A x. ( L ` B ) ) )

  disjoint A r
  disjoint F r
  disjoint L r
  disjoint M r
  disjoint ph r
  disjoint B r
  disjoint R r
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint N x
  disjoint N y
  disjoint O y
  disjoint O z
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint ps y
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint T y
  assert |- -. ph

  proof
    wph
    cB
    cF
    cfv
    #
    cM
    cfv
    #
    cA
    cB
    cL
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    wph
    cA
    cR
    cmul
    co
    #
    @1
    cdiv
    co
    #
    vr
    cv
    #
    clt
    wbr
    #
    @7
    cR
    @2
    cdiv
    co
    #
    clt
    wbr
    #
    wa
    #
    @4
    vr
    cq
    wph
    @7
    cq
    wcel
    #
    wa
    #
    @11
    wa
    #
    @8
    @4
    @13
    @8
    @10
    simprl
    #
    @14
    @7
    @6
    @12
    @7
    cr
    wcel
    #
    wph
    @11
    @7
    qre
    ad2antlr
    #
    wph
    @6
    cr
    wcel
    #
    @12
    @11
    wph
    @5
    @1
    wph
    cA
    cR
    nmoleub2lem3.1
    wph
    cR
    nmoleub2.r
    rpred
    #
    remulcld
    #
    wph
    @1
    wph
    cT
    cngp
    wcel
    #
    @0
    cT
    cbs
    cfv
    #
    wcel
    #
    @1
    cr
    wcel
    #
    wph
    cT
    cnlm
    wcel
    #
    @21
    wph
    cnlm
    cclm
    cT
    nmoleub2.t
    elin1d
    #
    cT
    nlmngp
    syl
    wph
    cV
    @22
    cB
    cF
    wph
    cF
    cS
    cT
    clmhm
    co
    wcel
    #
    cV
    @22
    cF
    wf
    nmoleub2.f
    cV
    @22
    cS
    cT
    cF
    nmoleub2.v
    @22
    eqid
    #
    lmhmf
    syl
    nmoleub2lem3.3
    ffvelrnd
    #
    @0
    cT
    cM
    @22
    @28
    nmoleub2.m
    nmcl
    syl2anc
    #
    wph
    cc0
    @3
    @1
    wph
    0red
    wph
    cA
    @2
    nmoleub2lem3.1
    wph
    cS
    cngp
    wcel
    #
    cB
    cV
    wcel
    #
    @2
    cr
    wcel
    #
    wph
    cS
    cnlm
    wcel
    #
    @31
    wph
    cnlm
    cclm
    cS
    nmoleub2.s
    elin1d
    #
    cS
    nlmngp
    syl
    #
    nmoleub2lem3.3
    cB
    cS
    cL
    cV
    nmoleub2.v
    nmoleub2.l
    nmcl
    syl2anc
    #
    remulcld
    #
    @30
    wph
    cA
    @2
    nmoleub2lem3.1
    @37
    nmoleub2lem3.2
    wph
    @31
    @32
    cc0
    @2
    cle
    wbr
    @36
    nmoleub2lem3.3
    cB
    cS
    cL
    cV
    nmoleub2.v
    nmoleub2.l
    nmge0
    syl2anc
    mulge0d
    wph
    @3
    @1
    clt
    wbr
    @4
    wn
    nmoleub2lem3.6
    wph
    @3
    @1
    @38
    @30
    ltnled
    mpbird
    #
    lelttrd
    #
    elrpd
    rerpdivcld
    #
    ad2antrr
    #
    @14
    @7
    @1
    cmul
    co
    #
    @5
    cle
    wbr
    #
    @7
    @6
    cle
    wbr
    #
    @14
    @43
    cR
    cdiv
    co
    #
    cA
    cle
    wbr
    @44
    @14
    @7
    cB
    c.x
    co
    #
    cF
    cfv
    #
    cM
    cfv
    #
    cR
    cdiv
    co
    #
    @46
    cA
    cle
    @14
    @49
    @43
    cR
    cdiv
    @14
    @49
    @7
    @0
    cT
    cvsca
    cfv
    #
    co
    #
    cM
    cfv
    #
    @7
    cT
    csca
    cfv
    #
    cnm
    cfv
    #
    cfv
    #
    @1
    cmul
    co
    #
    @43
    @14
    @48
    @52
    cM
    @14
    @27
    @7
    cK
    wcel
    #
    @32
    @48
    @52
    wceq
    wph
    @27
    @12
    @11
    nmoleub2.f
    ad2antrr
    #
    @13
    @58
    @11
    wph
    cq
    cK
    @7
    nmoleub2a.5
    sselda
    adantr
    #
    wph
    @32
    @12
    @11
    nmoleub2lem3.3
    ad2antrr
    #
    cK
    cS
    cT
    c.x
    @51
    cV
    cF
    cG
    @7
    cB
    nmoleub2.g
    nmoleub2.w
    nmoleub2.v
    nmoleub2lem3.p
    @51
    eqid
    #
    lmhmlin
    syl3anc
    fveq2d
    @14
    @25
    @7
    @54
    cbs
    cfv
    #
    wcel
    @23
    @53
    @57
    wceq
    wph
    @25
    @12
    @11
    @26
    ad2antrr
    @14
    @7
    cK
    @63
    @60
    @14
    @63
    cG
    cbs
    cfv
    cK
    @14
    @54
    cG
    cbs
    @14
    @27
    @54
    cG
    wceq
    @59
    cS
    cT
    cF
    cG
    @54
    nmoleub2.g
    @54
    eqid
    #
    lmhmsca
    syl
    #
    fveq2d
    nmoleub2.w
    syl6eqr
    eleqtrrd
    wph
    @23
    @12
    @11
    @29
    ad2antrr
    @55
    @51
    @54
    @63
    cM
    @22
    cT
    @7
    @0
    @28
    nmoleub2.m
    @62
    @64
    @63
    eqid
    @55
    eqid
    nmvs
    syl3anc
    @14
    @56
    @7
    @1
    cmul
    @14
    @56
    @7
    cG
    cnm
    cfv
    #
    cfv
    #
    @7
    @14
    @7
    @55
    @66
    @14
    @54
    cG
    cnm
    @65
    fveq2d
    fveq1d
    @14
    @7
    cabs
    cfv
    #
    @67
    @7
    @14
    cS
    cclm
    wcel
    #
    @58
    @68
    @67
    wceq
    wph
    @69
    @12
    @11
    wph
    cnlm
    cclm
    cS
    nmoleub2.s
    elin2d
    ad2antrr
    #
    @60
    @7
    cG
    cK
    cS
    nmoleub2.g
    nmoleub2.w
    clmabs
    syl2anc
    @14
    @7
    @17
    @14
    cc0
    @7
    @14
    0red
    #
    @17
    @14
    cc0
    @6
    @7
    @71
    @42
    @17
    wph
    cc0
    @6
    cle
    wbr
    #
    @12
    @11
    wph
    @5
    cr
    wcel
    #
    cc0
    @5
    cle
    wbr
    @24
    cc0
    @1
    clt
    wbr
    #
    @72
    @20
    wph
    cA
    cR
    nmoleub2lem3.1
    @19
    nmoleub2lem3.2
    wph
    cR
    nmoleub2.r
    rpge0d
    mulge0d
    @30
    @40
    @5
    @1
    divge0
    syl22anc
    ad2antrr
    @15
    lelttrd
    ltled
    absidd
    eqtr3d
    #
    eqtrd
    oveq1d
    3eqtrd
    oveq1d
    @14
    @47
    cV
    wcel
    #
    @47
    cL
    cfv
    #
    cR
    clt
    wbr
    #
    @50
    cA
    cle
    wbr
    #
    @14
    @69
    @58
    @32
    @76
    @70
    @60
    @61
    @7
    c.x
    cG
    cK
    cV
    cS
    cB
    nmoleub2.v
    nmoleub2.g
    nmoleub2lem3.p
    nmoleub2.w
    clmvscl
    syl3anc
    @14
    @77
    @7
    @2
    cmul
    co
    #
    cR
    clt
    @14
    @77
    @67
    @2
    cmul
    co
    #
    @80
    @14
    @34
    @58
    @32
    @77
    @81
    wceq
    wph
    @34
    @12
    @11
    @35
    ad2antrr
    @60
    @61
    @66
    c.x
    cG
    cK
    cL
    cV
    cS
    @7
    cB
    nmoleub2.v
    nmoleub2.l
    nmoleub2lem3.p
    nmoleub2.g
    nmoleub2.w
    @66
    eqid
    nmvs
    syl3anc
    @14
    @67
    @7
    @2
    cmul
    @75
    oveq1d
    eqtrd
    @14
    @80
    cR
    clt
    wbr
    #
    @10
    @13
    @8
    @10
    simprr
    @14
    @16
    cR
    cr
    wcel
    #
    @33
    cc0
    @2
    clt
    wbr
    wa
    #
    @82
    @10
    wb
    @17
    wph
    @83
    @12
    @11
    @19
    ad2antrr
    #
    wph
    @84
    @12
    @11
    wph
    @2
    wph
    @31
    @32
    cB
    cS
    c0g
    cfv
    #
    wne
    @2
    crp
    wcel
    @36
    nmoleub2lem3.3
    nmoleub2lem3.4
    cB
    cS
    cL
    cV
    @86
    nmoleub2.v
    nmoleub2.l
    @86
    eqid
    nmrpcl
    syl3anc
    #
    rpregt0d
    #
    ad2antrr
    @7
    cR
    @2
    ltmuldiv
    syl3anc
    mpbird
    eqbrtrd
    wph
    @76
    @78
    @79
    wi
    wi
    @12
    @11
    nmoleub2lem3.5
    ad2antrr
    mp2d
    eqbrtrrd
    @14
    @43
    cA
    cR
    @14
    @7
    @1
    @17
    wph
    @24
    @12
    @11
    @30
    ad2antrr
    remulcld
    wph
    cA
    cr
    wcel
    @12
    @11
    nmoleub2lem3.1
    ad2antrr
    #
    wph
    cR
    crp
    wcel
    @12
    @11
    nmoleub2.r
    ad2antrr
    ledivmul2d
    mpbid
    @14
    @16
    @73
    @24
    @74
    wa
    #
    @44
    @45
    wb
    @17
    @14
    cA
    cR
    @89
    @85
    remulcld
    wph
    @90
    @12
    @11
    wph
    @24
    @74
    @30
    @40
    jca
    #
    ad2antrr
    @7
    @5
    @1
    lemuldiv
    syl3anc
    mpbid
    lensymd
    pm2.21dd
    wph
    @18
    @9
    cr
    wcel
    @6
    @9
    clt
    wbr
    #
    @11
    vr
    cq
    wrex
    @41
    wph
    cR
    @2
    @19
    @87
    rerpdivcld
    wph
    @5
    @2
    cmul
    co
    #
    cR
    @1
    cmul
    co
    #
    clt
    wbr
    #
    @92
    wph
    @93
    cR
    @3
    cmul
    co
    #
    @94
    clt
    wph
    cA
    cc
    wcel
    #
    cR
    cc
    wcel
    #
    @2
    cc
    wcel
    #
    @93
    @96
    wceq
    wph
    cA
    nmoleub2lem3.1
    recnd
    wph
    cR
    @19
    recnd
    wph
    @2
    @37
    recnd
    @97
    @98
    @99
    w3a
    @93
    cA
    cR
    @2
    cmul
    co
    cmul
    co
    @96
    cA
    cR
    @2
    mulass
    cA
    cR
    @2
    mul12
    eqtrd
    syl3anc
    wph
    @3
    @1
    cR
    @38
    @30
    nmoleub2.r
    @39
    ltmul2dd
    eqbrtrd
    wph
    @73
    @84
    @83
    @90
    @95
    @92
    wb
    @20
    @88
    @19
    @91
    @5
    @2
    cR
    @1
    lt2mul2div
    syl22anc
    mpbid
    vr
    @6
    @9
    qbtwnre
    syl3anc
    r19.29a
    nmoleub2lem3.6
    pm2.65i
end
