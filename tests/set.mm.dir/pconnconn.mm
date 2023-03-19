include "cpconn.mm"
include "wcel.mm"
include "cconn.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cin.mm"
include "wceq.mm"
include "w3a.mm"
include "cun.mm"
include "cuni.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "df-3an.mm"
include "wex.mm"
include "n0.mm"
include "anbi12i.mm"
include "eeanv.mm"
include "bitr4i.mm"
include "cc0.mm"
include "cfv.mm"
include "c1.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "wrex.mm"
include "simpll.mm"
include "simprll.mm"
include "simplrl.mm"
include "elunii.mm"
include "syl2anc.mm"
include "simprlr.mm"
include "simplrr.mm"
include "eqid.mm"
include "pconncn.mm"
include "syl3anc.mm"
include "wn.mm"
include "adantl.mm"
include "cicc.mm"
include "wf.mm"
include "iiuni.mm"
include "iiconn.mm"
include "a1i.mm"
include "adantr.mm"
include "cdif.mm"
include "ccld.mm"
include "uncom.mm"
include "simprr.mm"
include "syl5eq.mm"
include "wss.mm"
include "wb.mm"
include "elssuni.mm"
include "syl.mm"
include "incom.mm"
include "uneqdifeq.mm"
include "mpbid.mm"
include "ctop.mm"
include "pconntop.mm"
include "ad3antrrr.mm"
include "opncld.mm"
include "eqeltrrd.mm"
include "0elunit.mm"
include "eqeltrd.mm"
include "conncn.mm"
include "1elunit.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "inelcm.mm"
include "pm2.21ddne.mm"
include "expr.mm"
include "pm2.01d.mm"
include "neqned.mm"
include "rexlimddv.mm"
include "exp32.mm"
include "exlimdvv.mm"
include "syl5bi.mm"
include "impd.mm"
include "ralrimivva.mm"
include "ctopon.mm"
include "toptopon.mm"
include "sylib.mm"
include "dfconn2.mm"
include "mpbird.mm"

theorem pconnconn
  let cJ: class J
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vg: setvar g
  let vh: setvar h
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cR: class R
  let cS: class S
  let vi: setvar i
  let cA: class A
  let cF: class F
  let cV: class V


  assert |- ( J e. PConn -> J e. Conn )

  proof
    cJ
    cpconn
    wcel
    #
    cJ
    cconn
    wcel
    #
    vx
    cv
    #
    c0
    wne
    #
    vy
    cv
    #
    c0
    wne
    #
    @2
    @4
    cin
    #
    c0
    wceq
    #
    w3a
    #
    @2
    @4
    cun
    #
    cJ
    cuni
    #
    wne
    #
    wi
    #
    vy
    cJ
    wral
    vx
    cJ
    wral
    #
    @0
    @12
    vx
    vy
    cJ
    cJ
    @8
    @3
    @5
    wa
    #
    @7
    wa
    @0
    @2
    cJ
    wcel
    #
    @4
    cJ
    wcel
    #
    wa
    #
    wa
    #
    @11
    @3
    @5
    @7
    df-3an
    @18
    @14
    @7
    @11
    @14
    va
    cv
    #
    @2
    wcel
    #
    vb
    cv
    #
    @4
    wcel
    #
    wa
    #
    vb
    wex
    va
    wex
    #
    @18
    @7
    @11
    wi
    #
    @14
    @20
    va
    wex
    #
    @22
    vb
    wex
    #
    wa
    @24
    @3
    @26
    @5
    @27
    va
    @2
    n0
    vb
    @4
    n0
    anbi12i
    @20
    @22
    va
    vb
    eeanv
    bitr4i
    @18
    @23
    @25
    va
    vb
    @18
    @23
    @7
    @11
    @18
    @23
    @7
    wa
    #
    wa
    #
    cc0
    vf
    cv
    #
    cfv
    #
    @19
    wceq
    #
    c1
    @30
    cfv
    #
    @21
    wceq
    #
    wa
    #
    @11
    vf
    cii
    cJ
    ccn
    co
    #
    @29
    @0
    @19
    @10
    wcel
    #
    @21
    @10
    wcel
    #
    @35
    vf
    @36
    wrex
    @0
    @17
    @28
    simpll
    @29
    @20
    @15
    @37
    @18
    @20
    @22
    @7
    simprll
    #
    @0
    @15
    @16
    @28
    simplrl
    #
    @19
    @2
    cJ
    elunii
    syl2anc
    @29
    @22
    @16
    @38
    @18
    @20
    @22
    @7
    simprlr
    #
    @0
    @15
    @16
    @28
    simplrr
    #
    @21
    @4
    cJ
    elunii
    syl2anc
    @19
    @21
    vf
    cJ
    @10
    @10
    eqid
    #
    pconncn
    syl3anc
    @29
    @30
    @36
    wcel
    #
    @35
    wa
    #
    wa
    #
    @9
    @10
    @46
    @9
    @10
    wceq
    #
    @29
    @45
    @47
    @47
    wn
    #
    @29
    @45
    @47
    wa
    #
    wa
    #
    @48
    @6
    c0
    @18
    @23
    @7
    @49
    simplrr
    #
    @50
    @21
    @2
    wcel
    @22
    @6
    c0
    wne
    @50
    @33
    @21
    @2
    @49
    @34
    @29
    @44
    @32
    @34
    @47
    simplrr
    adantl
    @50
    cc0
    c1
    cicc
    co
    #
    @2
    @30
    wf
    c1
    @52
    wcel
    @33
    @2
    wcel
    @50
    cc0
    @2
    @30
    cii
    cJ
    @52
    iiuni
    cii
    cconn
    wcel
    @50
    iiconn
    a1i
    @29
    @44
    @35
    @47
    simprll
    @29
    @15
    @49
    @40
    adantr
    @50
    @10
    @4
    cdif
    #
    @2
    cJ
    ccld
    cfv
    #
    @50
    @4
    @2
    cun
    #
    @10
    wceq
    #
    @53
    @2
    wceq
    #
    @50
    @55
    @9
    @10
    @4
    @2
    uncom
    @29
    @45
    @47
    simprr
    syl5eq
    @50
    @4
    @10
    wss
    #
    @4
    @2
    cin
    #
    c0
    wceq
    @56
    @57
    wb
    @50
    @16
    @58
    @29
    @16
    @49
    @42
    adantr
    #
    @4
    cJ
    elssuni
    syl
    @50
    @59
    @6
    c0
    @4
    @2
    incom
    @51
    syl5eq
    @4
    @2
    @10
    uneqdifeq
    syl2anc
    mpbid
    @50
    cJ
    ctop
    wcel
    #
    @16
    @53
    @54
    wcel
    @0
    @61
    @17
    @28
    @49
    cJ
    pconntop
    #
    ad3antrrr
    @60
    @4
    cJ
    @10
    @43
    opncld
    syl2anc
    eqeltrrd
    cc0
    @52
    wcel
    @50
    0elunit
    a1i
    @50
    @31
    @19
    @2
    @49
    @32
    @29
    @44
    @32
    @34
    @47
    simplrl
    adantl
    @29
    @20
    @49
    @39
    adantr
    eqeltrd
    conncn
    1elunit
    @52
    @2
    c1
    @30
    ffvelrn
    sylancl
    eqeltrrd
    @29
    @22
    @49
    @41
    adantr
    @21
    @2
    @4
    inelcm
    syl2anc
    pm2.21ddne
    expr
    pm2.01d
    neqned
    rexlimddv
    exp32
    exlimdvv
    syl5bi
    impd
    syl5bi
    ralrimivva
    @0
    cJ
    @10
    ctopon
    cfv
    wcel
    #
    @1
    @13
    wb
    @0
    @61
    @63
    @62
    cJ
    @10
    @43
    toptopon
    sylib
    vx
    vy
    cJ
    @10
    dfconn2
    syl
    mpbird
end
