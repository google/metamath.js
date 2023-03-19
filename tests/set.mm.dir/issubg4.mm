include "cgrp.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "w3a.mm"
include "subgss.mm"
include "c0g.mm"
include "eqid.mm"
include "subg0cl.mm"
include "ne0i.mm"
include "syl.mm"
include "subgsubcl.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "3jca.mm"
include "cplusg.mm"
include "cminusg.mm"
include "wa.mm"
include "simplrl.mm"
include "simplrr.mm"
include "wrex.mm"
include "simprr.mm"
include "r19.2z.mm"
include "sylan.mm"
include "wi.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "adantl.mm"
include "simprl.mm"
include "sselda.mm"
include "grpsubid.mm"
include "adantlr.mm"
include "syldan.mm"
include "sylibd.mm"
include "rexlimdva.mm"
include "imp.mm"
include "simpr.mm"
include "oveq1.mm"
include "ralbidv.mm"
include "sylc.mm"
include "wb.mm"
include "grpidcl.mm"
include "ad2antrr.mm"
include "grpsubval.mm"
include "syl2anc.mm"
include "simpll.mm"
include "grpinvcl.mm"
include "grplid.mm"
include "eqtrd.mm"
include "ralbidva.mm"
include "adantr.mm"
include "mpbid.mm"
include "fveq2.mm"
include "rspccva.mm"
include "ad2ant2l.mm"
include "simplll.mm"
include "sseldd.mm"
include "grpsubinv.mm"
include "anassrs.mm"
include "ralrimdva.mm"
include "ralimdva.mm"
include "impancom.mm"
include "mpd.mm"
include "cbvralv.mm"
include "sylib.mm"
include "r19.26.mm"
include "sylanbrc.mm"
include "exp42.mm"
include "3impd.mm"
include "issubg2.mm"
include "sylibrd.mm"
include "impbid2.mm"

theorem issubg4
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cS: class S
  let cG: class G
  let c.mi: class .-
  let vz: setvar z
  assume issubg4.b: |- B = ( Base ` G )
  assume issubg4.p: |- .- = ( -g ` G )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint G x
  disjoint G y
  disjoint .- x
  disjoint .- y
  disjoint S x
  disjoint S y
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint G z
  disjoint .- z
  disjoint S z
  assert |- ( G e. Grp -> ( S e. ( SubGrp ` G ) <-> ( S C_ B /\ S =/= (/) /\ A. x e. S A. y e. S ( x .- y ) e. S ) ) )

  proof
    cG
    cgrp
    wcel
    #
    cS
    cG
    csubg
    cfv
    wcel
    #
    cS
    cB
    wss
    #
    cS
    c0
    wne
    #
    vx
    cv
    #
    vy
    cv
    #
    c.mi
    co
    #
    cS
    wcel
    #
    vy
    cS
    wral
    #
    vx
    cS
    wral
    #
    w3a
    #
    @1
    @2
    @3
    @9
    cB
    cS
    cG
    issubg4.b
    subgss
    @1
    cG
    c0g
    cfv
    #
    cS
    wcel
    #
    @3
    cS
    cG
    @11
    @11
    eqid
    #
    subg0cl
    cS
    @11
    ne0i
    syl
    @1
    @7
    vx
    vy
    cS
    cS
    @1
    @4
    cS
    wcel
    #
    @5
    cS
    wcel
    #
    @7
    cS
    cG
    c.mi
    @4
    @5
    issubg4.p
    subgsubcl
    3expb
    ralrimivva
    3jca
    @0
    @10
    @2
    @3
    @5
    vz
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cS
    wcel
    #
    vz
    cS
    wral
    #
    @5
    cG
    cminusg
    cfv
    #
    cfv
    #
    cS
    wcel
    #
    wa
    vy
    cS
    wral
    #
    w3a
    #
    @1
    @0
    @2
    @3
    @9
    @25
    @0
    @2
    @3
    @9
    @25
    @0
    @2
    @3
    wa
    #
    wa
    #
    @9
    wa
    #
    @2
    @3
    @24
    @0
    @2
    @3
    @9
    simplrl
    @0
    @2
    @3
    @9
    simplrr
    @28
    @20
    vy
    cS
    wral
    #
    @23
    vy
    cS
    wral
    #
    @24
    @28
    @4
    @16
    @17
    co
    #
    cS
    wcel
    #
    vz
    cS
    wral
    #
    vx
    cS
    wral
    #
    @29
    @28
    @30
    @34
    @28
    @11
    @5
    c.mi
    co
    #
    cS
    wcel
    #
    vy
    cS
    wral
    #
    @30
    @28
    @12
    @9
    @37
    @27
    @9
    @8
    vx
    cS
    wrex
    #
    @12
    @27
    @3
    @9
    @38
    @0
    @2
    @3
    simprr
    @8
    vx
    cS
    r19.2z
    sylan
    @27
    @38
    @12
    @27
    @8
    @12
    vx
    cS
    @27
    @14
    wa
    #
    @8
    @4
    @4
    c.mi
    co
    #
    cS
    wcel
    #
    @12
    @14
    @8
    @41
    wi
    @27
    @7
    @41
    vy
    @4
    cS
    @5
    @4
    wceq
    @6
    @40
    cS
    @5
    @4
    @4
    c.mi
    oveq2
    eleq1d
    rspcv
    adantl
    @39
    @40
    @11
    cS
    @27
    @14
    @4
    cB
    wcel
    #
    @40
    @11
    wceq
    #
    @27
    cS
    cB
    @4
    @0
    @2
    @3
    simprl
    #
    sselda
    @0
    @42
    @43
    @26
    cB
    cG
    c.mi
    @4
    @11
    issubg4.b
    @13
    issubg4.p
    grpsubid
    adantlr
    syldan
    eleq1d
    sylibd
    rexlimdva
    imp
    syldan
    @27
    @9
    simpr
    @8
    @37
    vx
    @11
    cS
    @4
    @11
    wceq
    #
    @7
    @36
    vy
    cS
    @45
    @6
    @35
    cS
    @4
    @11
    @5
    c.mi
    oveq1
    eleq1d
    ralbidv
    rspcv
    sylc
    @27
    @37
    @30
    wb
    @9
    @27
    @36
    @23
    vy
    cS
    @27
    @15
    wa
    #
    @35
    @22
    cS
    @46
    @35
    @11
    @22
    @17
    co
    #
    @22
    @46
    @11
    cB
    wcel
    #
    @5
    cB
    wcel
    #
    @35
    @47
    wceq
    @0
    @48
    @26
    @15
    cB
    cG
    @11
    issubg4.b
    @13
    grpidcl
    ad2antrr
    @27
    cS
    cB
    @5
    @44
    sselda
    #
    cB
    @17
    cG
    @21
    c.mi
    @11
    @5
    issubg4.b
    @17
    eqid
    #
    @21
    eqid
    #
    issubg4.p
    grpsubval
    syl2anc
    @46
    @0
    @22
    cB
    wcel
    #
    @47
    @22
    wceq
    @0
    @26
    @15
    simpll
    #
    @46
    @0
    @49
    @53
    @54
    @50
    cB
    cG
    @21
    @5
    issubg4.b
    @52
    grpinvcl
    syl2anc
    cB
    @17
    cG
    @22
    @11
    issubg4.b
    @51
    @13
    grplid
    syl2anc
    eqtrd
    eleq1d
    ralbidva
    adantr
    mpbid
    #
    @27
    @30
    @9
    @34
    @27
    @30
    wa
    #
    @8
    @33
    vx
    cS
    @56
    @14
    wa
    @8
    @32
    vz
    cS
    @56
    @14
    @16
    cS
    wcel
    #
    @8
    @32
    wi
    @56
    @14
    @57
    wa
    #
    wa
    #
    @8
    @4
    @16
    @21
    cfv
    #
    c.mi
    co
    #
    cS
    wcel
    #
    @32
    @59
    @60
    cS
    wcel
    #
    @8
    @62
    wi
    @30
    @57
    @63
    @27
    @14
    @23
    @63
    vy
    @16
    cS
    @5
    @16
    wceq
    @22
    @60
    cS
    @5
    @16
    @21
    fveq2
    eleq1d
    rspccva
    ad2ant2l
    @7
    @62
    vy
    @60
    cS
    @5
    @60
    wceq
    @6
    @61
    cS
    @5
    @60
    @4
    c.mi
    oveq2
    eleq1d
    rspcv
    syl
    @59
    @61
    @31
    cS
    @59
    cB
    @17
    cG
    c.mi
    @21
    @4
    @16
    issubg4.b
    @51
    issubg4.p
    @52
    @0
    @26
    @30
    @58
    simplll
    @59
    cS
    cB
    @4
    @56
    @2
    @58
    @0
    @2
    @3
    @30
    simplrl
    adantr
    #
    @56
    @14
    @57
    simprl
    sseldd
    @59
    cS
    cB
    @16
    @64
    @56
    @14
    @57
    simprr
    sseldd
    grpsubinv
    eleq1d
    sylibd
    anassrs
    ralrimdva
    ralimdva
    impancom
    mpd
    @33
    @20
    vx
    vy
    cS
    @4
    @5
    wceq
    #
    @32
    @19
    vz
    cS
    @65
    @31
    @18
    cS
    @4
    @5
    @16
    @17
    oveq1
    eleq1d
    ralbidv
    cbvralv
    sylib
    @55
    @20
    @23
    vy
    cS
    r19.26
    sylanbrc
    3jca
    exp42
    3impd
    vy
    vz
    cB
    @17
    cS
    cG
    @21
    issubg4.b
    @51
    @52
    issubg2
    sylibrd
    impbid2
end
