include "cdomn.mm"
include "wcel.mm"
include "csn.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "wrex.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wi.mm"
include "crg.mm"
include "domnring.mm"
include "3ad2ant1.mm"
include "simp2l.mm"
include "simp2r.mm"
include "lidlnz.mm"
include "syl3anc.mm"
include "weq.mm"
include "oveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "oveq1.mm"
include "anbi12d.mm"
include "rspcva.mm"
include "cbs.mm"
include "cfv.mm"
include "adantr.mm"
include "wss.mm"
include "eqid.mm"
include "lidlss.mm"
include "3ad2ant2.mm"
include "sseld.mm"
include "com12.mm"
include "impcom.mm"
include "ringlidm.mm"
include "syl2anc.mm"
include "wb.mm"
include "eqeq2.mm"
include "eqcoms.mm"
include "adantl.mm"
include "csg.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "syl.mm"
include "a1i.mm"
include "3imp.mm"
include "ringcl.mm"
include "ringidcl.mm"
include "grpsubeq0.mm"
include "rngsubdir.mm"
include "eqeq1d.mm"
include "wo.mm"
include "simpl1.mm"
include "3jca.mm"
include "grpsubcl.mm"
include "domneq0.mm"
include "biimpd.mm"
include "eqneqall.mm"
include "jaod.mm"
include "sylbid.mm"
include "sylbird.mm"
include "mpdan.mm"
include "ex.mm"
include "com13.mm"
include "expd.mm"
include "pm2.43b.mm"
include "com14.mm"
include "imp.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem lidldomn1
  let vx: setvar x
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let c.1: class .1.
  let cI: class I
  let cL: class L
  let c.0: class .0.
  let vy: setvar y
  let vk: setvar k
  assume lidldomn1.l: |- L = ( LIdeal ` R )
  assume lidldomn1.t: |- .x. = ( .r ` R )
  assume lidldomn1.1: |- .1. = ( 1r ` R )
  assume lidldomn1.0: |- .0. = ( 0g ` R )

  disjoint I x
  disjoint U x
  disjoint .x. x
  disjoint I y
  disjoint x y
  disjoint L y
  disjoint R y
  disjoint U y
  disjoint .0. y
  disjoint .1. y
  disjoint .x. y
  disjoint k x
  assert |- ( ( R e. Domn /\ ( U e. L /\ U =/= { .0. } ) /\ I e. U ) -> ( A. x e. U ( ( I .x. x ) = x /\ ( x .x. I ) = x ) -> I = .1. ) )

  proof
    cR
    cdomn
    wcel
    #
    cU
    cL
    wcel
    #
    cU
    c.0
    csn
    wne
    #
    wa
    #
    cI
    cU
    wcel
    #
    w3a
    #
    vy
    cv
    #
    c.0
    wne
    #
    vy
    cU
    wrex
    #
    cI
    vx
    cv
    #
    c.x
    co
    #
    @9
    wceq
    #
    @9
    cI
    c.x
    co
    #
    @9
    wceq
    #
    wa
    #
    vx
    cU
    wral
    #
    cI
    c.1
    wceq
    #
    wi
    #
    @5
    cR
    crg
    wcel
    #
    @1
    @2
    @8
    @0
    @3
    @18
    @4
    cR
    domnring
    #
    3ad2ant1
    #
    @0
    @1
    @2
    @4
    simp2l
    @0
    @1
    @2
    @4
    simp2r
    vy
    cR
    cL
    cU
    c.0
    lidldomn1.l
    lidldomn1.0
    lidlnz
    syl3anc
    @5
    @7
    @17
    vy
    cU
    @5
    @6
    cU
    wcel
    #
    @7
    @17
    wi
    @15
    @21
    @7
    @5
    @16
    @15
    @21
    @7
    @5
    @16
    wi
    #
    wi
    #
    @21
    @15
    @21
    @23
    wi
    #
    @21
    @15
    wa
    cI
    @6
    c.x
    co
    #
    @6
    wceq
    #
    @6
    cI
    c.x
    co
    #
    @6
    wceq
    #
    wa
    #
    @24
    @14
    @29
    vx
    @6
    cU
    vx
    vy
    weq
    #
    @11
    @26
    @13
    @28
    @30
    @10
    @25
    @9
    @6
    @9
    @6
    cI
    c.x
    oveq2
    @30
    id
    #
    eqeq12d
    @30
    @12
    @27
    @9
    @6
    @9
    @6
    cI
    c.x
    oveq1
    @31
    eqeq12d
    anbi12d
    rspcva
    @26
    @24
    @28
    @26
    @21
    @7
    @22
    @5
    @21
    @7
    wa
    #
    @26
    @16
    @5
    @32
    @26
    @16
    wi
    #
    @5
    @32
    wa
    #
    c.1
    @6
    c.x
    co
    #
    @6
    wceq
    #
    @33
    @34
    @18
    @6
    cR
    cbs
    cfv
    #
    wcel
    #
    @36
    @5
    @18
    @32
    @20
    adantr
    #
    @32
    @5
    @38
    @21
    @5
    @38
    wi
    @7
    @5
    @21
    @38
    @5
    cU
    @37
    @6
    @3
    @0
    cU
    @37
    wss
    #
    @4
    @1
    @40
    @2
    @37
    cU
    cL
    cR
    @37
    eqid
    #
    lidldomn1.l
    lidlss
    adantr
    #
    3ad2ant2
    sseld
    com12
    adantr
    impcom
    #
    @37
    cR
    c.x
    c.1
    @6
    @41
    lidldomn1.t
    lidldomn1.1
    ringlidm
    syl2anc
    @34
    @36
    wa
    @26
    @25
    @35
    wceq
    #
    @16
    @36
    @26
    @44
    wb
    #
    @34
    @45
    @6
    @35
    @6
    @35
    @25
    eqeq2
    eqcoms
    adantl
    @34
    @44
    @16
    wi
    @36
    @34
    @44
    @25
    @35
    cR
    csg
    cfv
    #
    co
    #
    c.0
    wceq
    #
    @16
    @34
    cR
    cgrp
    wcel
    #
    @25
    @37
    wcel
    #
    @35
    @37
    wcel
    #
    @48
    @44
    wb
    @5
    @49
    @32
    @0
    @3
    @49
    @4
    @0
    @18
    @49
    @19
    cR
    ringgrp
    syl
    3ad2ant1
    #
    adantr
    @34
    @18
    cI
    @37
    wcel
    #
    @38
    @50
    @39
    @5
    @53
    @32
    @0
    @3
    @4
    @53
    @3
    @4
    @53
    wi
    wi
    @0
    @3
    cU
    @37
    cI
    @42
    sseld
    a1i
    3imp
    #
    adantr
    #
    @43
    @37
    cR
    c.x
    cI
    @6
    @41
    lidldomn1.t
    ringcl
    syl3anc
    @34
    @18
    c.1
    @37
    wcel
    #
    @38
    @51
    @39
    @5
    @56
    @32
    @0
    @3
    @56
    @4
    @0
    @18
    @56
    @19
    @37
    cR
    c.1
    @41
    lidldomn1.1
    ringidcl
    syl
    3ad2ant1
    #
    adantr
    #
    @43
    @37
    cR
    c.x
    c.1
    @6
    @41
    lidldomn1.t
    ringcl
    syl3anc
    @37
    cR
    @46
    @25
    @35
    c.0
    @41
    lidldomn1.0
    @46
    eqid
    #
    grpsubeq0
    syl3anc
    @34
    @48
    cI
    c.1
    @46
    co
    #
    @6
    c.x
    co
    #
    c.0
    wceq
    #
    @16
    @34
    @61
    @47
    c.0
    @34
    @37
    cR
    c.x
    @46
    cI
    c.1
    @6
    @41
    lidldomn1.t
    @59
    @39
    @55
    @58
    @43
    rngsubdir
    eqeq1d
    @34
    @62
    @60
    c.0
    wceq
    #
    @6
    c.0
    wceq
    #
    wo
    #
    @16
    @34
    @0
    @60
    @37
    wcel
    #
    @38
    @62
    @65
    wb
    @0
    @3
    @4
    @32
    simpl1
    @34
    @49
    @53
    @56
    w3a
    #
    @66
    @5
    @67
    @32
    @5
    @49
    @53
    @56
    @52
    @54
    @57
    3jca
    adantr
    #
    @37
    cR
    @46
    cI
    c.1
    @41
    @59
    grpsubcl
    syl
    @43
    @37
    cR
    c.x
    @60
    @6
    c.0
    @41
    lidldomn1.t
    lidldomn1.0
    domneq0
    syl3anc
    @34
    @63
    @16
    @64
    @34
    @63
    @16
    @34
    @67
    @63
    @16
    wb
    @68
    @37
    cR
    @46
    cI
    c.1
    c.0
    @41
    lidldomn1.0
    @59
    grpsubeq0
    syl
    biimpd
    @32
    @64
    @16
    wi
    #
    @5
    @7
    @69
    @21
    @64
    @7
    @16
    @16
    @6
    c.0
    eqneqall
    com12
    adantl
    adantl
    jaod
    sylbid
    sylbird
    sylbird
    adantr
    sylbid
    mpdan
    ex
    com13
    expd
    adantr
    syl
    ex
    pm2.43b
    com14
    imp
    rexlimdva
    mpd
end
