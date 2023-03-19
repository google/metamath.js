include "co.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "cres.mm"
include "cgsu.mm"
include "cplusf.mm"
include "cfv.mm"
include "cmpt.mm"
include "ctopn.mm"
include "wss.mm"
include "crab.mm"
include "crn.mm"
include "cfg.mm"
include "cflf.mm"
include "cof.mm"
include "ctsu.mm"
include "wcel.mm"
include "wceq.mm"
include "ctmd.mm"
include "ctps.mm"
include "tmdtps.mm"
include "syl.mm"
include "tsmscl.mm"
include "sseldd.mm"
include "eqid.mm"
include "plusfval.mm"
include "syl2anc.mm"
include "ctopon.mm"
include "istps.mm"
include "sylib.mm"
include "cfbas.mm"
include "cfil.mm"
include "tsmsfbas.mm"
include "fgcl.mm"
include "tsmslem1.mm"
include "ccmn.mm"
include "tsmsval.mm"
include "eleqtrd.mm"
include "ctx.mm"
include "ccn.mm"
include "cop.mm"
include "cuni.mm"
include "ccnp.mm"
include "tmdcn.mm"
include "cxp.mm"
include "opelxpi.mm"
include "txtopon.mm"
include "toponuni.mm"
include "cncnpi.mm"
include "flfcnp2.mm"
include "eqeltrrd.mm"
include "cmnd.mm"
include "wa.mm"
include "cmnmnd.mm"
include "mndcl.mm"
include "3expb.mm"
include "sylan.mm"
include "inidm.mm"
include "off.mm"
include "c0g.mm"
include "adantr.mm"
include "elfpw.mm"
include "simprbi.mm"
include "adantl.mm"
include "wf.mm"
include "simplbi.mm"
include "fssres.mm"
include "syl2an.mm"
include "cvv.mm"
include "fvex.mm"
include "a1i.mm"
include "fdmfifsupp.mm"
include "gsumadd.mm"
include "cbs.mm"
include "eqeltri.mm"
include "fex2.mm"
include "syl3anc.mm"
include "offres.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "mpteq2dva.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "eleqtrrd.mm"

theorem tsmsadd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let vz: setvar z
  let vx: setvar x
  assume tsmsadd.b: |- B = ( Base ` G )
  assume tsmsadd.p: |- .+ = ( +g ` G )
  assume tsmsadd.1: |- ( ph -> G e. CMnd )
  assume tsmsadd.2: |- ( ph -> G e. TopMnd )
  assume tsmsadd.a: |- ( ph -> A e. V )
  assume tsmsadd.f: |- ( ph -> F : A --> B )
  assume tsmsadd.h: |- ( ph -> H : A --> B )
  assume tsmsadd.x: |- ( ph -> X e. ( G tsums F ) )
  assume tsmsadd.y: |- ( ph -> Y e. ( G tsums H ) )


  assert |- ( ph -> ( X .+ Y ) e. ( G tsums ( F oF .+ H ) ) )

  proof
    wph
    cX
    cY
    c.pl
    co
    #
    vz
    cA
    cpw
    cfn
    cin
    #
    cG
    cF
    vz
    cv
    #
    cres
    #
    cgsu
    co
    #
    cG
    cH
    @2
    cres
    #
    cgsu
    co
    #
    cG
    cplusf
    cfv
    #
    co
    #
    cmpt
    #
    cG
    ctopn
    cfv
    #
    @1
    vy
    @1
    vy
    cv
    #
    @2
    wss
    vz
    @1
    crab
    cmpt
    #
    crn
    #
    cfg
    co
    #
    cflf
    co
    #
    cfv
    #
    cG
    cF
    cH
    c.pl
    cof
    #
    co
    #
    ctsu
    co
    #
    wph
    cX
    cY
    @7
    co
    #
    @0
    @16
    wph
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    @20
    @0
    wceq
    wph
    cG
    cF
    ctsu
    co
    #
    cB
    cX
    wph
    cA
    cB
    cF
    cG
    cV
    tsmsadd.b
    tsmsadd.1
    wph
    cG
    ctmd
    wcel
    #
    cG
    ctps
    wcel
    #
    tsmsadd.2
    cG
    tmdtps
    syl
    #
    tsmsadd.a
    tsmsadd.f
    tsmscl
    tsmsadd.x
    sseldd
    #
    wph
    cG
    cH
    ctsu
    co
    #
    cB
    cY
    wph
    cA
    cB
    cH
    cG
    cV
    tsmsadd.b
    tsmsadd.1
    @26
    tsmsadd.a
    tsmsadd.h
    tsmscl
    tsmsadd.y
    sseldd
    #
    cB
    c.pl
    @7
    cG
    cX
    cY
    tsmsadd.b
    tsmsadd.p
    @7
    eqid
    #
    plusfval
    syl2anc
    wph
    vz
    @4
    @6
    cX
    cY
    @10
    @10
    @14
    @10
    @7
    cB
    cB
    @1
    wph
    @25
    @10
    cB
    ctopon
    cfv
    wcel
    #
    @26
    cB
    @10
    cG
    tsmsadd.b
    @10
    eqid
    #
    istps
    sylib
    #
    @33
    wph
    @13
    @1
    cfbas
    cfv
    wcel
    @14
    @1
    cfil
    cfv
    wcel
    wph
    vz
    vy
    cA
    @1
    @12
    @13
    cV
    @1
    eqid
    #
    @12
    eqid
    @13
    eqid
    #
    tsmsadd.a
    tsmsfbas
    @13
    @1
    fgcl
    syl
    wph
    cA
    cB
    @1
    cF
    cG
    cV
    @2
    tsmsadd.b
    @34
    tsmsadd.1
    tsmsadd.a
    tsmsadd.f
    tsmslem1
    #
    wph
    cA
    cB
    @1
    cH
    cG
    cV
    @2
    tsmsadd.b
    @34
    tsmsadd.1
    tsmsadd.a
    tsmsadd.h
    tsmslem1
    #
    wph
    cX
    @23
    vz
    @1
    @4
    cmpt
    @15
    cfv
    tsmsadd.x
    wph
    vz
    vy
    cA
    cB
    @1
    cF
    cG
    @10
    @13
    ccmn
    cV
    tsmsadd.b
    @32
    @34
    @35
    tsmsadd.1
    tsmsadd.a
    tsmsadd.f
    tsmsval
    eleqtrd
    wph
    cY
    @28
    vz
    @1
    @6
    cmpt
    @15
    cfv
    tsmsadd.y
    wph
    vz
    vy
    cA
    cB
    @1
    cH
    cG
    @10
    @13
    ccmn
    cV
    tsmsadd.b
    @32
    @34
    @35
    tsmsadd.1
    tsmsadd.a
    tsmsadd.h
    tsmsval
    eleqtrd
    wph
    @7
    @10
    @10
    ctx
    co
    #
    @10
    ccn
    co
    wcel
    #
    cX
    cY
    cop
    #
    @38
    cuni
    #
    wcel
    @7
    @40
    @38
    @10
    ccnp
    co
    cfv
    wcel
    wph
    @24
    @39
    tsmsadd.2
    @7
    cG
    @10
    @32
    @30
    tmdcn
    syl
    wph
    @40
    cB
    cB
    cxp
    #
    @41
    wph
    @21
    @22
    @40
    @42
    wcel
    @27
    @29
    cX
    cY
    cB
    cB
    opelxpi
    syl2anc
    wph
    @38
    @42
    ctopon
    cfv
    wcel
    #
    @42
    @41
    wceq
    wph
    @31
    @31
    @43
    @33
    @33
    @10
    @10
    cB
    cB
    txtopon
    syl2anc
    @42
    @38
    toponuni
    syl
    eleqtrd
    @40
    @7
    @38
    @10
    @41
    @41
    eqid
    cncnpi
    syl2anc
    flfcnp2
    eqeltrrd
    wph
    @19
    vz
    @1
    cG
    @18
    @2
    cres
    #
    cgsu
    co
    #
    cmpt
    #
    @15
    cfv
    @16
    wph
    vz
    vy
    cA
    cB
    @1
    @18
    cG
    @10
    @13
    ccmn
    cV
    tsmsadd.b
    @32
    @34
    @35
    tsmsadd.1
    tsmsadd.a
    wph
    vx
    vy
    cA
    cA
    cA
    c.pl
    cB
    cB
    cB
    cF
    cH
    cV
    cV
    wph
    cG
    cmnd
    wcel
    #
    vx
    cv
    #
    cB
    wcel
    #
    @11
    cB
    wcel
    #
    wa
    @48
    @11
    c.pl
    co
    cB
    wcel
    #
    wph
    cG
    ccmn
    wcel
    #
    @47
    tsmsadd.1
    cG
    cmnmnd
    syl
    @47
    @49
    @50
    @51
    cB
    c.pl
    cG
    @48
    @11
    tsmsadd.b
    tsmsadd.p
    mndcl
    3expb
    sylan
    tsmsadd.f
    tsmsadd.h
    tsmsadd.a
    tsmsadd.a
    cA
    inidm
    off
    tsmsval
    wph
    @46
    @9
    @15
    wph
    vz
    @1
    @45
    @8
    wph
    @2
    @1
    wcel
    #
    wa
    #
    cG
    @3
    @5
    @17
    co
    #
    cgsu
    co
    @4
    @6
    c.pl
    co
    #
    @45
    @8
    @54
    @2
    cB
    c.pl
    @3
    cG
    @5
    cfn
    cG
    c0g
    cfv
    #
    tsmsadd.b
    @57
    eqid
    tsmsadd.p
    wph
    @52
    @53
    tsmsadd.1
    adantr
    @53
    @2
    cfn
    wcel
    #
    wph
    @53
    @2
    cA
    wss
    #
    @58
    @2
    cA
    elfpw
    #
    simprbi
    adantl
    #
    wph
    cA
    cB
    cF
    wf
    #
    @59
    @2
    cB
    @3
    wf
    @53
    tsmsadd.f
    @53
    @59
    @58
    @60
    simplbi
    #
    cA
    cB
    @2
    cF
    fssres
    syl2an
    #
    wph
    cA
    cB
    cH
    wf
    #
    @59
    @2
    cB
    @5
    wf
    @53
    tsmsadd.h
    @63
    cA
    cB
    @2
    cH
    fssres
    syl2an
    #
    @54
    @2
    cB
    @3
    cvv
    @57
    @64
    @61
    @57
    cvv
    wcel
    @54
    cG
    c0g
    fvex
    a1i
    #
    fdmfifsupp
    @54
    @2
    cB
    @5
    cvv
    @57
    @66
    @61
    @67
    fdmfifsupp
    gsumadd
    @54
    @44
    @55
    cG
    cgsu
    wph
    @44
    @55
    wceq
    #
    @53
    wph
    cF
    cvv
    wcel
    #
    cH
    cvv
    wcel
    #
    @68
    wph
    @62
    cA
    cV
    wcel
    #
    cB
    cvv
    wcel
    #
    @69
    tsmsadd.f
    tsmsadd.a
    @72
    wph
    cB
    cG
    cbs
    cfv
    cvv
    tsmsadd.b
    cG
    cbs
    fvex
    eqeltri
    a1i
    #
    cA
    cB
    cF
    cV
    cvv
    fex2
    syl3anc
    wph
    @65
    @71
    @72
    @70
    tsmsadd.h
    tsmsadd.a
    @73
    cA
    cB
    cH
    cV
    cvv
    fex2
    syl3anc
    @2
    c.pl
    cF
    cH
    cvv
    cvv
    offres
    syl2anc
    adantr
    oveq2d
    @54
    @4
    cB
    wcel
    @6
    cB
    wcel
    @8
    @56
    wceq
    @36
    @37
    cB
    c.pl
    @7
    cG
    @4
    @6
    tsmsadd.b
    tsmsadd.p
    @30
    plusfval
    syl2anc
    3eqtr4d
    mpteq2dva
    fveq2d
    eqtrd
    eleqtrrd
end
