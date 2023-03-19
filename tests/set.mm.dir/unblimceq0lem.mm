include "cv.mm"
include "wne.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "w3a.mm"
include "wrex.mm"
include "crp.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "cif.mm"
include "wral.mm"
include "wceq.mm"
include "breq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "adantr.mm"
include "cc.mm"
include "wf.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "ffvelrnd.mm"
include "abscld.mm"
include "cr.mm"
include "simprl.mm"
include "rpred.mm"
include "readdcld.mm"
include "absge0d.mm"
include "cc0.mm"
include "rpgt0d.mm"
include "addgegt0d.mm"
include "elrpd.mm"
include "wn.mm"
include "simplrl.mm"
include "ifclda.mm"
include "rspcdva.mm"
include "simprr.mm"
include "rsp.mm"
include "sylc.mm"
include "wb.mm"
include "neeq1.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "fveq2.mm"
include "breq2d.mm"
include "3anbi123d.mm"
include "adantl.mm"
include "adantlr.mm"
include "iftrued.mm"
include "eqcomd.mm"
include "simprrr.mm"
include "eqbrtrd.mm"
include "lensymd.mm"
include "wi.mm"
include "ltaddposd.mm"
include "mpbid.mm"
include "ex.mm"
include "necon3bd.mm"
include "mpd.mm"
include "simprrl.mm"
include "addge02d.mm"
include "letrd.mm"
include "3jca.mm"
include "eqeltrrd.mm"
include "iffalsed.mm"
include "pm2.61dan.mm"
include "rspcedvd.mm"
include "rexlimddv.mm"
include "ralrimivva.mm"

theorem unblimceq0lem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cS: class S
  let cF: class F
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume unblimceq0lem.0: |- ( ph -> S C_ CC )
  assume unblimceq0lem.1: |- ( ph -> F : S --> CC )
  assume unblimceq0lem.2: |- ( ph -> A e. CC )
  assume unblimceq0lem.3: |- ( ph -> A. b e. RR+ A. d e. RR+ E. x e. S ( ( abs ` ( x - A ) ) < d /\ b <_ ( abs ` ( F ` x ) ) ) )

  disjoint A b
  disjoint A d
  disjoint A x
  disjoint b d
  disjoint b x
  disjoint d x
  disjoint A y
  disjoint d y
  disjoint x y
  disjoint F b
  disjoint F d
  disjoint F x
  disjoint F y
  disjoint S b
  disjoint S d
  disjoint S x
  disjoint S y
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint ph x
  disjoint b c
  disjoint c d
  disjoint c x
  disjoint ph y
  disjoint c y
  assert |- ( ph -> A. c e. RR+ A. d e. RR+ E. y e. S ( y =/= A /\ ( abs ` ( y - A ) ) < d /\ c <_ ( abs ` ( F ` y ) ) ) )

  proof
    wph
    vy
    cv
    #
    cA
    wne
    #
    @0
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    vd
    cv
    #
    clt
    wbr
    #
    vc
    cv
    #
    @0
    cF
    cfv
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    w3a
    #
    vy
    cS
    wrex
    #
    vc
    vd
    crp
    crp
    wph
    @6
    crp
    wcel
    #
    @4
    crp
    wcel
    #
    wa
    #
    wa
    #
    vx
    cv
    #
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    @4
    clt
    wbr
    #
    cA
    cS
    wcel
    #
    cA
    cF
    cfv
    #
    cabs
    cfv
    #
    @6
    caddc
    co
    #
    @6
    cif
    #
    @16
    cF
    cfv
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    wa
    #
    @11
    vx
    cS
    @15
    @28
    vx
    cS
    wrex
    #
    vd
    crp
    wral
    #
    @13
    @29
    @15
    @19
    vb
    cv
    #
    @26
    cle
    wbr
    #
    wa
    #
    vx
    cS
    wrex
    #
    vd
    crp
    wral
    #
    @30
    vb
    crp
    @24
    @31
    @24
    wceq
    #
    @34
    @29
    vd
    crp
    @36
    @33
    @28
    vx
    cS
    @36
    @32
    @27
    @19
    @31
    @24
    @26
    cle
    breq1
    anbi2d
    rexbidv
    ralbidv
    wph
    @35
    vb
    crp
    wral
    @14
    unblimceq0lem.3
    adantr
    @15
    @20
    @23
    @6
    crp
    @15
    @20
    wa
    #
    @23
    @37
    @22
    @6
    @37
    @21
    @37
    cS
    cc
    cA
    cF
    wph
    cS
    cc
    cF
    wf
    #
    @14
    @20
    unblimceq0lem.1
    ad2antrr
    @15
    @20
    simpr
    ffvelrnd
    #
    abscld
    #
    @15
    @6
    cr
    wcel
    #
    @20
    @15
    @6
    wph
    @12
    @13
    simprl
    #
    rpred
    adantr
    #
    readdcld
    #
    @37
    @22
    @6
    @40
    @43
    @37
    @21
    @39
    absge0d
    @15
    cc0
    @6
    clt
    wbr
    #
    @20
    @15
    @6
    @42
    rpgt0d
    adantr
    #
    addgegt0d
    elrpd
    wph
    @12
    @13
    @20
    wn
    #
    simplrl
    ifclda
    rspcdva
    wph
    @12
    @13
    simprr
    @29
    vd
    crp
    rsp
    sylc
    @15
    @16
    cS
    wcel
    #
    @28
    wa
    #
    wa
    #
    @10
    @16
    cA
    wne
    #
    @19
    @6
    @26
    cle
    wbr
    #
    w3a
    #
    vy
    @16
    cS
    @15
    @48
    @28
    simprl
    #
    @0
    @16
    wceq
    #
    @10
    @53
    wb
    @50
    @55
    @1
    @51
    @5
    @19
    @9
    @52
    @0
    @16
    cA
    neeq1
    @55
    @3
    @18
    @4
    clt
    @55
    @2
    @17
    cabs
    @0
    @16
    cA
    cmin
    oveq1
    fveq2d
    breq1d
    @55
    @8
    @26
    @6
    cle
    @55
    @7
    @25
    cabs
    @0
    @16
    cF
    fveq2
    fveq2d
    breq2d
    3anbi123d
    adantl
    @50
    @20
    @53
    @50
    @20
    wa
    #
    @51
    @19
    @52
    @56
    @26
    @23
    clt
    wbr
    #
    wn
    @51
    @56
    @23
    @26
    @15
    @20
    @23
    cr
    wcel
    @49
    @44
    adantlr
    #
    @50
    @26
    cr
    wcel
    @20
    @50
    @25
    @50
    cS
    cc
    @16
    cF
    wph
    @38
    @14
    @49
    unblimceq0lem.1
    ad2antrr
    @54
    ffvelrnd
    abscld
    adantr
    #
    @56
    @23
    @24
    @26
    cle
    @56
    @24
    @23
    @56
    @20
    @23
    @6
    @50
    @20
    simpr
    iftrued
    eqcomd
    @50
    @27
    @20
    @15
    @48
    @19
    @27
    simprrr
    #
    adantr
    eqbrtrd
    #
    lensymd
    @56
    @57
    @16
    cA
    @15
    @20
    @16
    cA
    wceq
    #
    @57
    wi
    @49
    @37
    @62
    @57
    @37
    @62
    wa
    @26
    @22
    @23
    clt
    @62
    @26
    @22
    wceq
    @37
    @62
    @25
    @21
    cabs
    @16
    cA
    cF
    fveq2
    fveq2d
    adantl
    @37
    @22
    @23
    clt
    wbr
    #
    @62
    @37
    @45
    @63
    @46
    @37
    @6
    @22
    @43
    @40
    ltaddposd
    mpbid
    adantr
    eqbrtrd
    ex
    adantlr
    necon3bd
    mpd
    @50
    @19
    @20
    @15
    @48
    @19
    @27
    simprrl
    #
    adantr
    @56
    @6
    @23
    @26
    @15
    @20
    @41
    @49
    @43
    adantlr
    #
    @58
    @59
    @56
    cc0
    @22
    cle
    wbr
    @6
    @23
    cle
    wbr
    @56
    @21
    @15
    @20
    @21
    cc
    wcel
    @49
    @39
    adantlr
    absge0d
    @56
    @6
    @22
    @65
    @15
    @20
    @22
    cr
    wcel
    @49
    @40
    adantlr
    addge02d
    mpbid
    @61
    letrd
    3jca
    @50
    @47
    wa
    #
    @51
    @19
    @52
    @66
    @47
    @51
    @50
    @47
    simpr
    #
    @66
    @20
    @16
    cA
    @66
    @62
    @20
    @66
    @62
    wa
    @16
    cA
    cS
    @66
    @62
    simpr
    @66
    @48
    @62
    @50
    @48
    @47
    @54
    adantr
    adantr
    eqeltrrd
    ex
    necon3bd
    mpd
    @50
    @19
    @47
    @64
    adantr
    @66
    @6
    @24
    @26
    cle
    @66
    @24
    @6
    @66
    @20
    @23
    @6
    @67
    iffalsed
    eqcomd
    @50
    @27
    @47
    @60
    adantr
    eqbrtrd
    3jca
    pm2.61dan
    rspcedvd
    rexlimddv
    ralrimivva
end
