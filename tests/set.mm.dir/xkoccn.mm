include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "cxko.mm"
include "co.mm"
include "ccn.mm"
include "wf.mm"
include "ccnv.mm"
include "cima.mm"
include "crest.mm"
include "ccmp.mm"
include "cuni.mm"
include "cpw.mm"
include "crab.mm"
include "wss.mm"
include "cmpt2.mm"
include "crn.mm"
include "wral.mm"
include "cnconst2.mm"
include "3expa.mm"
include "eqid.mm"
include "fmptd.mm"
include "wceq.mm"
include "wrex.mm"
include "xkobval.mm"
include "abeq2i.mm"
include "c0.mm"
include "adantlr.mm"
include "simplr.mm"
include "imaeq2d.mm"
include "ima0.mm"
include "0ss.mm"
include "eqsstri.mm"
include "syl6eqss.mm"
include "imaeq1.mm"
include "sseq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "ralrimiva.mm"
include "rabid2.mm"
include "sylibr.mm"
include "simpllr.mm"
include "toponmax.mm"
include "syl.mm"
include "adantr.mm"
include "eqeltrrd.mm"
include "wne.mm"
include "cin.mm"
include "cif.mm"
include "ifnefalse.mm"
include "ad2antlr.mm"
include "eleq2d.mm"
include "vex.mm"
include "snss.mm"
include "syl6bb.mm"
include "cres.mm"
include "df-ima.mm"
include "simplrl.mm"
include "ad2antrr.mm"
include "elpwid.mm"
include "toponuni.mm"
include "ad5antr.mm"
include "sseqtr4d.mm"
include "xpssres.mm"
include "rneqd.mm"
include "syl5eq.mm"
include "rnxp.mm"
include "eqtrd.mm"
include "biantrurd.mm"
include "3bitr2d.mm"
include "bitr3d.mm"
include "syl6bbr.mm"
include "rabbi2dva.mm"
include "simplrr.mm"
include "toponss.mm"
include "syl2anc.mm"
include "sseqin2.mm"
include "sylib.mm"
include "eqtr3d.mm"
include "eqeltrd.mm"
include "pm2.61dane.mm"
include "imaeq2.mm"
include "mptpreima.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "rexlimdvva.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "cvv.mm"
include "simpr.mm"
include "ovex.mm"
include "pwex.mm"
include "xkotf.mm"
include "frn.mm"
include "ax-mp.mm"
include "ssexi.mm"
include "a1i.mm"
include "ctop.mm"
include "cfi.mm"
include "ctg.mm"
include "topontop.mm"
include "xkoval.mm"
include "syl2an.mm"
include "xkotopon.mm"
include "subbascn.mm"
include "mpbir2and.mm"

theorem xkoccn
  let vx: setvar x
  let cR: class R
  let cS: class S
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vk: setvar k
  let vv: setvar v
  let vy: setvar y
  let vz: setvar z

  disjoint R x
  disjoint S x
  disjoint X x
  disjoint Y x
  disjoint f k
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint R f
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint R k
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint R v
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint R y
  disjoint R z
  disjoint S f
  disjoint S k
  disjoint S v
  disjoint S y
  disjoint S z
  disjoint X f
  disjoint X k
  disjoint X v
  disjoint X y
  disjoint X z
  disjoint Y k
  disjoint Y v
  disjoint Y y
  assert |- ( ( R e. ( TopOn ` X ) /\ S e. ( TopOn ` Y ) ) -> ( x e. Y |-> ( X X. { x } ) ) e. ( S Cn ( S ^ko R ) ) )

  proof
    cR
    cX
    ctopon
    cfv
    wcel
    #
    cS
    cY
    ctopon
    cfv
    wcel
    #
    wa
    #
    vx
    cY
    cX
    vx
    cv
    #
    csn
    #
    cxp
    #
    cmpt
    #
    cS
    cS
    cR
    cxko
    co
    #
    ccn
    co
    wcel
    cY
    cR
    cS
    ccn
    co
    #
    @6
    wf
    @6
    ccnv
    #
    vy
    cv
    #
    cima
    #
    cS
    wcel
    #
    vy
    vk
    vv
    cR
    vz
    cv
    crest
    co
    ccmp
    wcel
    vz
    cR
    cuni
    #
    cpw
    #
    crab
    #
    cS
    vf
    cv
    #
    vk
    cv
    #
    cima
    #
    vv
    cv
    #
    wss
    #
    vf
    @8
    crab
    #
    cmpt2
    #
    crn
    #
    wral
    @2
    vx
    cY
    @5
    @8
    @6
    @0
    @1
    @3
    cY
    wcel
    #
    @5
    @8
    wcel
    #
    @3
    cR
    cS
    cX
    cY
    cnconst2
    3expa
    #
    @6
    eqid
    #
    fmptd
    @2
    @12
    vy
    @23
    @10
    @23
    wcel
    cR
    @17
    crest
    co
    ccmp
    wcel
    #
    @10
    @21
    wceq
    #
    wa
    #
    vv
    cS
    wrex
    vk
    @14
    wrex
    #
    @2
    @12
    @31
    vy
    @23
    vz
    vv
    cR
    cS
    @22
    vf
    vk
    @15
    @13
    vy
    @13
    eqid
    #
    @15
    eqid
    #
    @22
    eqid
    #
    xkobval
    abeq2i
    @2
    @30
    @12
    vk
    vv
    @14
    cS
    @2
    @17
    @14
    wcel
    #
    @19
    cS
    wcel
    #
    wa
    #
    wa
    #
    @28
    @29
    @12
    @38
    @28
    wa
    #
    @12
    @29
    @5
    @21
    wcel
    #
    vx
    cY
    crab
    #
    cS
    wcel
    #
    @39
    @42
    @17
    c0
    @39
    @17
    c0
    wceq
    #
    wa
    #
    cY
    @41
    cS
    @44
    @40
    vx
    cY
    wral
    cY
    @41
    wceq
    @44
    @40
    vx
    cY
    @44
    @24
    wa
    #
    @25
    @5
    @17
    cima
    #
    @19
    wss
    #
    @40
    @39
    @24
    @25
    @43
    @38
    @24
    @25
    @28
    @2
    @24
    @25
    @37
    @26
    adantlr
    adantlr
    #
    adantlr
    @45
    @46
    @5
    c0
    cima
    #
    @19
    @45
    @17
    c0
    @5
    @39
    @43
    @24
    simplr
    imaeq2d
    @49
    c0
    @19
    @5
    ima0
    @19
    0ss
    eqsstri
    syl6eqss
    @20
    @47
    vf
    @5
    @8
    @16
    @5
    wceq
    @18
    @46
    @19
    @16
    @5
    @17
    imaeq1
    sseq1d
    elrab
    #
    sylanbrc
    ralrimiva
    @40
    vx
    cY
    rabid2
    sylibr
    @39
    cY
    cS
    wcel
    #
    @43
    @39
    @1
    @51
    @0
    @1
    @37
    @28
    simpllr
    #
    cY
    cS
    toponmax
    syl
    adantr
    eqeltrrd
    @39
    @17
    c0
    wne
    #
    wa
    #
    @41
    @19
    cS
    @54
    cY
    @19
    cin
    #
    @41
    @19
    @54
    @40
    vx
    cY
    @19
    @54
    @24
    wa
    #
    @3
    @19
    wcel
    #
    @25
    @47
    wa
    #
    @40
    @56
    @3
    @43
    cY
    @19
    cif
    #
    wcel
    #
    @57
    @58
    @56
    @59
    @19
    @3
    @53
    @59
    @19
    wceq
    @39
    @24
    @17
    c0
    cY
    @19
    ifnefalse
    ad2antlr
    eleq2d
    #
    @56
    @60
    @4
    @19
    wss
    #
    @47
    @58
    @56
    @60
    @57
    @62
    @61
    @3
    @19
    vx
    vex
    snss
    syl6bb
    @56
    @46
    @4
    @19
    @56
    @46
    @17
    @4
    cxp
    #
    crn
    #
    @4
    @56
    @46
    @5
    @17
    cres
    #
    crn
    @64
    @5
    @17
    df-ima
    @56
    @65
    @63
    @56
    @17
    cX
    wss
    @65
    @63
    wceq
    @56
    @17
    @13
    cX
    @56
    @17
    @13
    @39
    @35
    @53
    @24
    @2
    @35
    @36
    @28
    simplrl
    ad2antrr
    elpwid
    @0
    cX
    @13
    wceq
    @1
    @37
    @28
    @53
    @24
    cX
    cR
    toponuni
    ad5antr
    sseqtr4d
    cX
    @4
    @17
    xpssres
    syl
    rneqd
    syl5eq
    @53
    @64
    @4
    wceq
    @39
    @24
    @17
    @4
    rnxp
    ad2antlr
    eqtrd
    sseq1d
    @56
    @25
    @47
    @39
    @24
    @25
    @53
    @48
    adantlr
    biantrurd
    3bitr2d
    bitr3d
    @50
    syl6bbr
    rabbi2dva
    @54
    @19
    cY
    wss
    #
    @55
    @19
    wceq
    @39
    @66
    @53
    @39
    @1
    @36
    @66
    @52
    @2
    @35
    @36
    @28
    simplrr
    #
    @19
    cS
    cY
    toponss
    syl2anc
    adantr
    @19
    cY
    sseqin2
    sylib
    eqtr3d
    @39
    @36
    @53
    @67
    adantr
    eqeltrd
    pm2.61dane
    @29
    @11
    @41
    cS
    @29
    @11
    @9
    @21
    cima
    @41
    @10
    @21
    @9
    imaeq2
    vx
    cY
    @5
    @21
    @6
    @27
    mptpreima
    syl6eq
    eleq1d
    syl5ibrcom
    expimpd
    rexlimdvva
    syl5bi
    ralrimiv
    @2
    vy
    @23
    @6
    cS
    @7
    cvv
    cY
    @8
    @0
    @1
    simpr
    @23
    cvv
    wcel
    @2
    @23
    @8
    cpw
    #
    @8
    cR
    cS
    ccn
    ovex
    pwex
    @15
    cS
    cxp
    #
    @68
    @22
    wf
    @23
    @68
    wss
    vz
    vv
    cR
    cS
    @22
    vf
    vk
    @15
    @13
    @32
    @33
    @34
    xkotf
    @69
    @68
    @22
    frn
    ax-mp
    ssexi
    a1i
    @0
    cR
    ctop
    wcel
    #
    cS
    ctop
    wcel
    #
    @7
    @23
    cfi
    cfv
    ctg
    cfv
    wceq
    @1
    cX
    cR
    topontop
    #
    cY
    cS
    topontop
    #
    vz
    vv
    cR
    cS
    @22
    vf
    vk
    @15
    @13
    @32
    @33
    @34
    xkoval
    syl2an
    @0
    @70
    @71
    @7
    @8
    ctopon
    cfv
    wcel
    @1
    @72
    @73
    cR
    cS
    @7
    @7
    eqid
    xkotopon
    syl2an
    subbascn
    mpbir2and
end
