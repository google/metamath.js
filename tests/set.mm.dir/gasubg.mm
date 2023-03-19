include "cga.mm"
include "co.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "wa.mm"
include "cgrp.mm"
include "cvv.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "wf.mm"
include "c0g.mm"
include "cv.mm"
include "wceq.mm"
include "cplusg.mm"
include "wral.mm"
include "gaset.mm"
include "subggrp.mm"
include "anim12ci.mm"
include "eqid.mm"
include "gaf.mm"
include "adantr.mm"
include "wss.mm"
include "simpr.mm"
include "subgss.mm"
include "syl.mm"
include "xpss1.mm"
include "fssresd.mm"
include "subgbas.mm"
include "xpeq1d.mm"
include "feq2d.mm"
include "mpbid.mm"
include "subg0cl.mm"
include "ovres.mm"
include "syl2anc.mm"
include "subg0.mm"
include "oveq1d.mm"
include "gagrpid.mm"
include "adantlr.mm"
include "3eqtr3d.mm"
include "eqimss2.mm"
include "sselda.mm"
include "anim12dan.mm"
include "simprl.mm"
include "ad2antrr.mm"
include "ad3antlr.mm"
include "simprr.mm"
include "sseldd.mm"
include "fovrnd.mm"
include "oveq2d.mm"
include "simplll.mm"
include "gaass.mm"
include "syl13anc.mm"
include "3eqtr4d.mm"
include "subgcl.mm"
include "3expb.mm"
include "sylan.mm"
include "ressplusg.mm"
include "oveqd.mm"
include "3eqtr2rd.mm"
include "syldan.mm"
include "ralrimivva.mm"
include "jca.mm"
include "ralrimiva.mm"
include "isga.mm"
include "sylanbrc.mm"

theorem gasubg
  let c.po: class .(+)
  let cS: class S
  let cG: class G
  let cH: class H
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume gasubg.1: |- H = ( G |`s S )


  assert |- ( ( .(+) e. ( G GrpAct Y ) /\ S e. ( SubGrp ` G ) ) -> ( .(+) |` ( S X. Y ) ) e. ( H GrpAct Y ) )

  proof
    c.po
    cG
    cY
    cga
    co
    wcel
    #
    cS
    cG
    csubg
    cfv
    #
    wcel
    #
    wa
    #
    cH
    cgrp
    wcel
    #
    cY
    cvv
    wcel
    #
    wa
    cH
    cbs
    cfv
    #
    cY
    cxp
    #
    cY
    c.po
    cS
    cY
    cxp
    #
    cres
    #
    wf
    #
    cH
    c0g
    cfv
    #
    vx
    cv
    #
    @9
    co
    #
    @12
    wceq
    #
    vy
    cv
    #
    vz
    cv
    #
    cH
    cplusg
    cfv
    #
    co
    #
    @12
    @9
    co
    #
    @15
    @16
    @12
    @9
    co
    #
    @9
    co
    #
    wceq
    #
    vz
    @6
    wral
    vy
    @6
    wral
    #
    wa
    #
    vx
    cY
    wral
    #
    wa
    @9
    cH
    cY
    cga
    co
    wcel
    @0
    @5
    @2
    @4
    c.po
    cG
    cY
    gaset
    cS
    cG
    cH
    gasubg.1
    subggrp
    anim12ci
    @3
    @10
    @25
    @3
    @8
    cY
    @9
    wf
    @10
    @3
    cG
    cbs
    cfv
    #
    cY
    cxp
    #
    cY
    @8
    c.po
    @0
    @27
    cY
    c.po
    wf
    #
    @2
    c.po
    cG
    @26
    cY
    @26
    eqid
    #
    gaf
    adantr
    #
    @3
    cS
    @26
    wss
    #
    @8
    @27
    wss
    @3
    @2
    @31
    @0
    @2
    simpr
    #
    @26
    cS
    cG
    @29
    subgss
    #
    syl
    cS
    @26
    cY
    xpss1
    syl
    fssresd
    @3
    @8
    @7
    cY
    @9
    @3
    cS
    @6
    cY
    @3
    @2
    cS
    @6
    wceq
    #
    @32
    cS
    cG
    cH
    gasubg.1
    subgbas
    syl
    #
    xpeq1d
    feq2d
    mpbid
    @3
    @24
    vx
    cY
    @3
    @12
    cY
    wcel
    #
    wa
    #
    @14
    @23
    @37
    cG
    c0g
    cfv
    #
    @12
    @9
    co
    #
    @38
    @12
    c.po
    co
    #
    @13
    @12
    @37
    @38
    cS
    wcel
    #
    @36
    @39
    @40
    wceq
    @37
    @2
    @41
    @3
    @2
    @36
    @32
    adantr
    #
    cS
    cG
    @38
    @38
    eqid
    #
    subg0cl
    syl
    @3
    @36
    simpr
    #
    @38
    @12
    cS
    cY
    c.po
    ovres
    syl2anc
    @37
    @38
    @11
    @12
    @9
    @37
    @2
    @38
    @11
    wceq
    @42
    cS
    cG
    cH
    @38
    gasubg.1
    @43
    subg0
    syl
    oveq1d
    @0
    @36
    @40
    @12
    wceq
    @2
    @12
    c.po
    cG
    cY
    @38
    @43
    gagrpid
    adantlr
    3eqtr3d
    @37
    @22
    vy
    vz
    @6
    @6
    @37
    @15
    @6
    wcel
    #
    @16
    @6
    wcel
    #
    wa
    @15
    cS
    wcel
    #
    @16
    cS
    wcel
    #
    wa
    #
    @22
    @37
    @45
    @47
    @46
    @48
    @37
    @6
    cS
    @15
    @3
    @6
    cS
    wss
    #
    @36
    @3
    @34
    @50
    @35
    @6
    cS
    eqimss2
    syl
    adantr
    #
    sselda
    @37
    @6
    cS
    @16
    @51
    sselda
    anim12dan
    @37
    @49
    wa
    #
    @21
    @15
    @16
    cG
    cplusg
    cfv
    #
    co
    #
    @12
    c.po
    co
    #
    @54
    @12
    @9
    co
    #
    @19
    @52
    @15
    @16
    @12
    c.po
    co
    #
    @9
    co
    #
    @15
    @57
    c.po
    co
    #
    @21
    @55
    @52
    @47
    @57
    cY
    wcel
    @58
    @59
    wceq
    @37
    @47
    @48
    simprl
    #
    @52
    @16
    @12
    cY
    @26
    cY
    c.po
    @3
    @28
    @36
    @49
    @30
    ad2antrr
    @52
    cS
    @26
    @16
    @2
    @31
    @0
    @36
    @49
    @33
    ad3antlr
    #
    @37
    @47
    @48
    simprr
    #
    sseldd
    #
    @37
    @36
    @49
    @44
    adantr
    #
    fovrnd
    @15
    @57
    cS
    cY
    c.po
    ovres
    syl2anc
    @52
    @20
    @57
    @15
    @9
    @52
    @48
    @36
    @20
    @57
    wceq
    @62
    @64
    @16
    @12
    cS
    cY
    c.po
    ovres
    syl2anc
    oveq2d
    @52
    @0
    @15
    @26
    wcel
    @16
    @26
    wcel
    @36
    @55
    @59
    wceq
    @0
    @2
    @36
    @49
    simplll
    @52
    cS
    @26
    @15
    @61
    @60
    sseldd
    @63
    @64
    @15
    @16
    @12
    @53
    c.po
    cG
    @26
    cY
    @29
    @53
    eqid
    #
    gaass
    syl13anc
    3eqtr4d
    @52
    @54
    cS
    wcel
    #
    @36
    @56
    @55
    wceq
    @37
    @2
    @49
    @66
    @42
    @2
    @47
    @48
    @66
    @53
    cS
    cG
    @15
    @16
    @65
    subgcl
    3expb
    sylan
    @64
    @54
    @12
    cS
    cY
    c.po
    ovres
    syl2anc
    @52
    @54
    @18
    @12
    @9
    @52
    @53
    @17
    @15
    @16
    @2
    @53
    @17
    wceq
    @0
    @36
    @49
    cS
    @53
    cG
    cH
    @1
    gasubg.1
    @65
    ressplusg
    ad3antlr
    oveqd
    oveq1d
    3eqtr2rd
    syldan
    ralrimivva
    jca
    ralrimiva
    jca
    vx
    vy
    vz
    @17
    @9
    cH
    @6
    cY
    @11
    @6
    eqid
    @17
    eqid
    @11
    eqid
    isga
    sylanbrc
end
