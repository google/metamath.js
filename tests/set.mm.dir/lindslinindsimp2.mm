include "wcel.mm"
include "clmod.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "clspn.mm"
include "wn.mm"
include "wral.mm"
include "cpw.mm"
include "cfsupp.mm"
include "wbr.mm"
include "clinc.mm"
include "wceq.mm"
include "wi.mm"
include "cmap.mm"
include "simprl.mm"
include "wb.mm"
include "elpwg.mm"
include "ad2antrr.mm"
include "mpbird.mm"
include "wo.mm"
include "clinco.mm"
include "simplr.mm"
include "ssdifss.mm"
include "adantl.mm"
include "cvv.mm"
include "difexg.mm"
include "syl.mm"
include "eqid.mm"
include "lspeqlco.mm"
include "eleq2d.mm"
include "bicomd.mm"
include "syl2anc.mm"
include "notbid.mm"
include "wrex.mm"
include "c0g.mm"
include "lcoval.mm"
include "eqcomi.mm"
include "breq2i.mm"
include "anbi1i.mm"
include "rexbii.mm"
include "anbi2i.mm"
include "syl6bb.mm"
include "ianor.mm"
include "ralnex.mm"
include "ralbii.mm"
include "bitr3i.mm"
include "orbi2i.mm"
include "bitri.mm"
include "bitrd.mm"
include "2ralbidv.mm"
include "wfal.mm"
include "simpllr.mm"
include "eldifi.mm"
include "ssel2.mm"
include "ad2ant2lr.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "notnotd.mm"
include "nbfal.mm"
include "sylib.mm"
include "orbi1d.mm"
include "2ralbidva.mm"
include "r19.32v.mm"
include "falim.mm"
include "sneq.mm"
include "difeq2d.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "orbi2d.mm"
include "raleqbidv.mm"
include "ralbidv.mm"
include "rspcva.mm"
include "lindslinindsimp2lem5.mm"
include "expr.mm"
include "com14.mm"
include "ex.mm"
include "pm2.43a.mm"
include "imp.mm"
include "expdimp.mm"
include "ralrimdv.mm"
include "ralrimiva.mm"
include "expcom.mm"
include "jaoi.mm"
include "com12.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "impr.mm"
include "jca.mm"

theorem lindslinindsimp2
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cM: class M
  let cV: class V
  let c.0: class .0.
  let cZ: class Z
  let vs: setvar s
  let vg: setvar g
  let vz: setvar z
  let vk: setvar k
  assume lindslinind.r: |- R = ( Scalar ` M )
  assume lindslinind.b: |- B = ( Base ` R )
  assume lindslinind.0: |- .0. = ( 0g ` R )
  assume lindslinind.z: |- Z = ( 0g ` M )

  disjoint B f
  disjoint B s
  disjoint B y
  disjoint f s
  disjoint f y
  disjoint s y
  disjoint M f
  disjoint M s
  disjoint M y
  disjoint R f
  disjoint R x
  disjoint f x
  disjoint S f
  disjoint S s
  disjoint S x
  disjoint S y
  disjoint s x
  disjoint x y
  disjoint V s
  disjoint V y
  disjoint Z f
  disjoint Z s
  disjoint Z y
  disjoint .0. f
  disjoint .0. s
  disjoint .0. x
  disjoint .0. y
  disjoint R y
  disjoint B x
  disjoint M x
  disjoint R s
  disjoint V f
  disjoint V x
  disjoint Z x
  disjoint B g
  disjoint B z
  disjoint f g
  disjoint f z
  disjoint g s
  disjoint g y
  disjoint g z
  disjoint s z
  disjoint y z
  disjoint M g
  disjoint M z
  disjoint R z
  disjoint x z
  disjoint S g
  disjoint S z
  disjoint g x
  disjoint V g
  disjoint V z
  disjoint Z g
  disjoint .0. g
  disjoint .0. z
  disjoint R g
  disjoint Z z
  disjoint k x
  assert |- ( ( S e. V /\ M e. LMod ) -> ( ( S C_ ( Base ` M ) /\ A. s e. S A. y e. ( B \ { .0. } ) -. ( y ( .s ` M ) s ) e. ( ( LSpan ` M ) ` ( S \ { s } ) ) ) -> ( S e. ~P ( Base ` M ) /\ A. f e. ( B ^m S ) ( ( f finSupp .0. /\ ( f ( linC ` M ) S ) = Z ) -> A. x e. S ( f ` x ) = .0. ) ) ) )

  proof
    cS
    cV
    wcel
    #
    cM
    clmod
    wcel
    #
    wa
    #
    cS
    cM
    cbs
    cfv
    #
    wss
    #
    vy
    cv
    #
    vs
    cv
    #
    cM
    cvsca
    cfv
    #
    co
    #
    cS
    @6
    csn
    #
    cdif
    #
    cM
    clspn
    cfv
    cfv
    #
    wcel
    #
    wn
    #
    vy
    cB
    c.0
    csn
    #
    cdif
    #
    wral
    vs
    cS
    wral
    #
    wa
    #
    cS
    @3
    cpw
    #
    wcel
    #
    vf
    cv
    #
    c.0
    cfsupp
    wbr
    @20
    cS
    cM
    clinc
    cfv
    #
    co
    cZ
    wceq
    wa
    #
    vx
    cv
    #
    @20
    cfv
    c.0
    wceq
    #
    vx
    cS
    wral
    wi
    #
    vf
    cB
    cS
    cmap
    co
    #
    wral
    #
    wa
    @2
    @17
    wa
    #
    @19
    @27
    @28
    @19
    @4
    @2
    @4
    @16
    simprl
    @0
    @19
    @4
    wb
    @1
    @17
    cS
    @3
    cV
    elpwg
    ad2antrr
    mpbird
    @2
    @4
    @16
    @27
    @2
    @4
    wa
    #
    @16
    @8
    @3
    wcel
    #
    wn
    #
    vg
    cv
    #
    c.0
    cfsupp
    wbr
    #
    wn
    #
    @8
    @32
    @10
    @21
    co
    #
    wceq
    #
    wn
    #
    wo
    #
    vg
    cB
    @10
    cmap
    co
    #
    wral
    #
    wo
    #
    vy
    @15
    wral
    vs
    cS
    wral
    #
    @27
    @29
    @13
    @41
    vs
    vy
    cS
    @15
    @29
    @13
    @8
    cM
    @10
    clinco
    co
    #
    wcel
    #
    wn
    #
    @41
    @29
    @12
    @44
    @29
    @1
    @10
    @18
    wcel
    #
    @12
    @44
    wb
    @0
    @1
    @4
    simplr
    #
    @29
    @46
    @10
    @3
    wss
    #
    @4
    @48
    @2
    cS
    @3
    @9
    ssdifss
    adantl
    @29
    @10
    cvv
    wcel
    #
    @46
    @48
    wb
    @0
    @49
    @1
    @4
    cS
    @9
    cV
    difexg
    ad2antrr
    @10
    @3
    cvv
    elpwg
    syl
    mpbird
    #
    @1
    @46
    wa
    #
    @44
    @12
    @51
    @43
    @11
    @8
    @3
    cM
    @10
    @3
    eqid
    #
    lspeqlco
    eleq2d
    bicomd
    syl2anc
    notbid
    @29
    @45
    @30
    @33
    @36
    wa
    #
    vg
    @39
    wrex
    #
    wa
    #
    wn
    #
    @41
    @29
    @44
    @55
    @29
    @1
    @46
    @44
    @55
    wb
    @47
    @50
    @51
    @44
    @30
    @32
    cR
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    @36
    wa
    #
    vg
    @39
    wrex
    #
    wa
    @55
    @3
    @8
    cB
    cR
    cM
    @10
    clmod
    vg
    @52
    lindslinind.r
    lindslinind.b
    lcoval
    @60
    @54
    @30
    @59
    @53
    vg
    @39
    @58
    @33
    @36
    @57
    c.0
    @32
    cfsupp
    c.0
    @57
    lindslinind.0
    eqcomi
    breq2i
    anbi1i
    rexbii
    anbi2i
    syl6bb
    syl2anc
    notbid
    @56
    @31
    @54
    wn
    #
    wo
    @41
    @30
    @54
    ianor
    @61
    @40
    @31
    @61
    @53
    wn
    #
    vg
    @39
    wral
    @40
    @53
    vg
    @39
    ralnex
    @62
    @38
    vg
    @39
    @33
    @36
    ianor
    ralbii
    bitr3i
    orbi2i
    bitri
    syl6bb
    bitrd
    2ralbidv
    @29
    @42
    wfal
    @40
    wo
    #
    vy
    @15
    wral
    #
    vs
    cS
    wral
    #
    @27
    @29
    @41
    @63
    vs
    vy
    cS
    @15
    @29
    @6
    cS
    wcel
    #
    @5
    @15
    wcel
    #
    wa
    #
    wa
    #
    @31
    wfal
    @40
    @69
    @31
    wn
    @31
    wfal
    wb
    @69
    @30
    @69
    @1
    @5
    cB
    wcel
    #
    @6
    @3
    wcel
    #
    @30
    @0
    @1
    @4
    @68
    simpllr
    @68
    @70
    @29
    @67
    @70
    @66
    @5
    cB
    @14
    eldifi
    adantl
    adantl
    @4
    @66
    @71
    @2
    @67
    cS
    @3
    @6
    ssel2
    ad2ant2lr
    @5
    @7
    cR
    cB
    @3
    cM
    @6
    @52
    lindslinind.r
    @7
    eqid
    lindslinind.b
    lmodvscl
    syl3anc
    notnotd
    @31
    nbfal
    sylib
    orbi1d
    2ralbidva
    @65
    wfal
    @40
    vy
    @15
    wral
    #
    vs
    cS
    wral
    #
    wo
    #
    @29
    @27
    @65
    wfal
    @72
    wo
    #
    vs
    cS
    wral
    @74
    @64
    @75
    vs
    cS
    wfal
    @40
    vy
    @15
    r19.32v
    ralbii
    wfal
    @72
    vs
    cS
    r19.32v
    bitri
    @74
    @29
    @27
    wfal
    @29
    @27
    wi
    #
    @73
    @76
    falim
    @29
    @73
    @27
    @29
    @73
    wa
    #
    @25
    vf
    @26
    @77
    @20
    @26
    wcel
    #
    wa
    @22
    @24
    vx
    cS
    @77
    @78
    @22
    @23
    cS
    wcel
    #
    @24
    wi
    #
    @29
    @73
    @78
    @22
    wa
    #
    @80
    wi
    @79
    @73
    @81
    @29
    @24
    @73
    @79
    @81
    @29
    @24
    wi
    wi
    #
    @79
    @73
    @79
    @82
    wi
    #
    @79
    @73
    wa
    @34
    @5
    @23
    @7
    co
    #
    @32
    cS
    @23
    csn
    #
    cdif
    #
    @21
    co
    #
    wceq
    #
    wn
    #
    wo
    #
    vg
    cB
    @86
    cmap
    co
    #
    wral
    #
    vy
    @15
    wral
    #
    @83
    @72
    @93
    vs
    @23
    cS
    @6
    @23
    wceq
    #
    @40
    @92
    vy
    @15
    @94
    @38
    @90
    vg
    @39
    @91
    @94
    @10
    @86
    cB
    cmap
    @94
    @9
    @85
    cS
    @6
    @23
    sneq
    difeq2d
    #
    oveq2d
    @94
    @37
    @89
    @34
    @94
    @36
    @88
    @94
    @8
    @84
    @35
    @87
    @6
    @23
    @5
    @7
    oveq2
    @94
    @10
    @86
    @32
    @21
    @95
    oveq2d
    eqeq12d
    notbid
    orbi2d
    raleqbidv
    ralbidv
    rspcva
    @29
    @79
    @81
    @93
    @24
    @2
    @4
    @79
    @81
    @93
    @24
    wi
    wi
    vx
    vy
    cB
    cR
    cS
    vf
    vg
    cM
    cV
    c.0
    cZ
    lindslinind.r
    lindslinind.b
    lindslinind.0
    lindslinind.z
    lindslinindsimp2lem5
    expr
    com14
    syl
    ex
    pm2.43a
    com14
    imp
    expdimp
    ralrimdv
    ralrimiva
    expcom
    jaoi
    com12
    syl5bi
    sylbid
    sylbid
    impr
    jca
    ex
end
