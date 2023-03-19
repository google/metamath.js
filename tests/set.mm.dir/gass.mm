include "cga.mm"
include "co.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cxp.mm"
include "cres.mm"
include "cv.mm"
include "wral.mm"
include "wceq.mm"
include "ovres.mm"
include "adantl.mm"
include "wf.mm"
include "gaf.mm"
include "fovrnda.mm"
include "eqeltrrd.mm"
include "ralrimivva.mm"
include "cgrp.mm"
include "cvv.mm"
include "c0g.mm"
include "cfv.mm"
include "cplusg.mm"
include "gagrp.mm"
include "ad2antrr.mm"
include "gaset.mm"
include "adantr.mm"
include "simpr.mm"
include "ssexd.mm"
include "jca.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "simplr.mm"
include "xpss2.mm"
include "fnssres.mm"
include "syl2anc.mm"
include "eleq1d.mm"
include "ralbidva.mm"
include "ralbiia.mm"
include "sylibr.mm"
include "ffnov.mm"
include "sylanbrc.mm"
include "eqid.mm"
include "grpidcl.mm"
include "sylan.mm"
include "sselda.mm"
include "simpll.mm"
include "gagrpid.mm"
include "syldan.mm"
include "eqtrd.mm"
include "simprl.mm"
include "simprr.mm"
include "gaass.mm"
include "syl13anc.mm"
include "simpllr.mm"
include "ovrspc2v.mm"
include "syl21anc.mm"
include "eqtr4d.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "ralrimiva.mm"
include "isga.mm"
include "impbida.mm"

theorem gass
  let vx: setvar x
  let vy: setvar y
  let c.po: class .(+)
  let cG: class G
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  assume gass.1: |- X = ( Base ` G )

  disjoint x y
  disjoint G x
  disjoint G y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint Z x
  disjoint Z y
  disjoint .(+) x
  disjoint .(+) y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint G u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint G v
  disjoint x z
  disjoint y z
  disjoint G z
  disjoint X u
  disjoint X v
  disjoint X z
  disjoint Y u
  disjoint Y v
  disjoint Y z
  disjoint Z u
  disjoint Z v
  disjoint Z z
  disjoint .(+) u
  disjoint .(+) v
  disjoint .(+) z
  assert |- ( ( .(+) e. ( G GrpAct Y ) /\ Z C_ Y ) -> ( ( .(+) |` ( X X. Z ) ) e. ( G GrpAct Z ) <-> A. x e. X A. y e. Z ( x .(+) y ) e. Z ) )

  proof
    c.po
    cG
    cY
    cga
    co
    wcel
    #
    cZ
    cY
    wss
    #
    wa
    #
    c.po
    cX
    cZ
    cxp
    #
    cres
    #
    cG
    cZ
    cga
    co
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    c.po
    co
    #
    cZ
    wcel
    #
    vy
    cZ
    wral
    #
    vx
    cX
    wral
    #
    @2
    @5
    wa
    #
    @9
    vx
    vy
    cX
    cZ
    @12
    @6
    cX
    wcel
    #
    @7
    cZ
    wcel
    wa
    #
    wa
    @6
    @7
    @4
    co
    #
    @8
    cZ
    @14
    @15
    @8
    wceq
    @12
    @6
    @7
    cX
    cZ
    c.po
    ovres
    #
    adantl
    @12
    @6
    @7
    cZ
    cX
    cZ
    @4
    @5
    @3
    cZ
    @4
    wf
    #
    @2
    @4
    cG
    cX
    cZ
    gass.1
    gaf
    adantl
    fovrnda
    eqeltrrd
    ralrimivva
    @2
    @11
    wa
    #
    cG
    cgrp
    wcel
    #
    cZ
    cvv
    wcel
    #
    wa
    @17
    cG
    c0g
    cfv
    #
    vz
    cv
    #
    @4
    co
    #
    @22
    wceq
    #
    vu
    cv
    #
    vv
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @22
    @4
    co
    #
    @25
    @26
    @22
    @4
    co
    #
    @4
    co
    #
    wceq
    #
    vv
    cX
    wral
    vu
    cX
    wral
    #
    wa
    #
    vz
    cZ
    wral
    #
    wa
    @5
    @18
    @19
    @20
    @0
    @19
    @1
    @11
    c.po
    cG
    cY
    gagrp
    ad2antrr
    #
    @2
    @20
    @11
    @2
    cZ
    cY
    cvv
    @0
    cY
    cvv
    wcel
    @1
    c.po
    cG
    cY
    gaset
    adantr
    @0
    @1
    simpr
    ssexd
    adantr
    jca
    @18
    @17
    @35
    @18
    @4
    @3
    wfn
    #
    @15
    cZ
    wcel
    #
    vy
    cZ
    wral
    #
    vx
    cX
    wral
    #
    @17
    @18
    c.po
    cX
    cY
    cxp
    #
    wfn
    #
    @3
    @41
    wss
    #
    @37
    @18
    @41
    cY
    c.po
    wf
    #
    @42
    @0
    @44
    @1
    @11
    c.po
    cG
    cX
    cY
    gass.1
    gaf
    ad2antrr
    @41
    cY
    c.po
    ffn
    syl
    @18
    @1
    @43
    @0
    @1
    @11
    simplr
    #
    cZ
    cY
    cX
    xpss2
    syl
    @41
    @3
    c.po
    fnssres
    syl2anc
    @18
    @11
    @40
    @2
    @11
    simpr
    @39
    @10
    vx
    cX
    @13
    @38
    @9
    vy
    cZ
    @14
    @15
    @8
    cZ
    @16
    eleq1d
    ralbidva
    ralbiia
    sylibr
    vx
    vy
    cX
    cZ
    cZ
    @4
    ffnov
    sylanbrc
    @18
    @34
    vz
    cZ
    @18
    @22
    cZ
    wcel
    #
    wa
    #
    @24
    @33
    @47
    @23
    @21
    @22
    c.po
    co
    #
    @22
    @18
    @21
    cX
    wcel
    #
    @46
    @23
    @48
    wceq
    @18
    @19
    @49
    @36
    cX
    cG
    @21
    gass.1
    @21
    eqid
    #
    grpidcl
    syl
    @21
    @22
    cX
    cZ
    c.po
    ovres
    sylan
    @18
    @46
    @22
    cY
    wcel
    #
    @48
    @22
    wceq
    #
    @18
    cZ
    cY
    @22
    @45
    sselda
    #
    @18
    @0
    @51
    @52
    @0
    @1
    @11
    simpll
    #
    @22
    c.po
    cG
    cY
    @21
    @50
    gagrpid
    sylan
    syldan
    eqtrd
    @47
    @32
    vu
    vv
    cX
    cX
    @47
    @25
    cX
    wcel
    #
    @26
    cX
    wcel
    #
    wa
    #
    wa
    #
    @28
    @22
    c.po
    co
    #
    @25
    @26
    @22
    c.po
    co
    #
    @4
    co
    #
    @29
    @31
    @58
    @59
    @25
    @60
    c.po
    co
    #
    @61
    @58
    @0
    @55
    @56
    @51
    @59
    @62
    wceq
    @18
    @0
    @46
    @57
    @54
    ad2antrr
    @47
    @55
    @56
    simprl
    #
    @47
    @55
    @56
    simprr
    #
    @47
    @51
    @57
    @53
    adantr
    @25
    @26
    @22
    @27
    c.po
    cG
    cX
    cY
    gass.1
    @27
    eqid
    #
    gaass
    syl13anc
    @58
    @55
    @60
    cZ
    wcel
    #
    @61
    @62
    wceq
    @63
    @58
    @56
    @46
    @11
    @66
    @64
    @18
    @46
    @57
    simplr
    #
    @2
    @11
    @46
    @57
    simpllr
    vx
    vy
    cX
    cZ
    cZ
    c.po
    @26
    @22
    ovrspc2v
    syl21anc
    @25
    @60
    cX
    cZ
    c.po
    ovres
    syl2anc
    eqtr4d
    @58
    @28
    cX
    wcel
    #
    @46
    @29
    @59
    wceq
    @58
    @19
    @55
    @56
    @68
    @18
    @19
    @46
    @57
    @36
    ad2antrr
    @63
    @64
    cX
    @27
    cG
    @25
    @26
    gass.1
    @65
    grpcl
    syl3anc
    @67
    @28
    @22
    cX
    cZ
    c.po
    ovres
    syl2anc
    @58
    @30
    @60
    @25
    @4
    @58
    @56
    @46
    @30
    @60
    wceq
    @64
    @67
    @26
    @22
    cX
    cZ
    c.po
    ovres
    syl2anc
    oveq2d
    3eqtr4d
    ralrimivva
    jca
    ralrimiva
    jca
    vz
    vu
    vv
    @27
    @4
    cG
    cX
    cZ
    @21
    gass.1
    @65
    @50
    isga
    sylanbrc
    impbida
end
