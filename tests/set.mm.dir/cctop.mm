include "wcel.mm"
include "cv.mm"
include "cdif.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "cpw.mm"
include "crab.mm"
include "ctop.mm"
include "cuni.mm"
include "ctopon.mm"
include "cfv.mm"
include "wss.mm"
include "wi.mm"
include "wal.mm"
include "cin.mm"
include "wral.mm"
include "wa.mm"
include "uniss.mm"
include "ssrab2.mm"
include "sspwuni.mm"
include "mpbi.mm"
include "syl6ss.mm"
include "vuniex.mm"
include "elpw.mm"
include "sylibr.mm"
include "wn.mm"
include "wrex.mm"
include "uni0c.mm"
include "notbii.mm"
include "rexnal.mm"
include "bitr4i.mm"
include "ssel2.mm"
include "difeq2.mm"
include "breq1d.mm"
include "eqeq1.mm"
include "orbi12d.mm"
include "elrab.mm"
include "sylib.mm"
include "simprd.mm"
include "ord.mm"
include "con1d.mm"
include "imp.mm"
include "cvv.mm"
include "ctex.mm"
include "adantl.mm"
include "simpllr.mm"
include "elssuni.mm"
include "sscon.mm"
include "3syl.mm"
include "ssdomg.mm"
include "sylc.mm"
include "domtr.mm"
include "sylancom.mm"
include "mpdan.mm"
include "exp31.mm"
include "rexlimdv.mm"
include "syl5bi.mm"
include "orrd.mm"
include "sylanbrc.mm"
include "ax-gen.mm"
include "ssinss1.mm"
include "vex.mm"
include "inex1.mm"
include "3imtr4i.mm"
include "ad2antrr.mm"
include "cun.mm"
include "difindi.mm"
include "unctb.mm"
include "syl5eqbr.mm"
include "orcd.mm"
include "ineq1.mm"
include "0in.mm"
include "syl6eq.mm"
include "olcd.mm"
include "ineq2.mm"
include "in0.mm"
include "ccase2.mm"
include "ad2ant2l.mm"
include "jca.mm"
include "syl2anb.mm"
include "rgen2a.mm"
include "pm3.2i.mm"
include "wb.mm"
include "pwexg.mm"
include "rabexg.mm"
include "istopg.mm"
include "mpbiri.mm"
include "pwidg.mm"
include "omex.mm"
include "0dom.mm"
include "orci.mm"
include "a1i.mm"
include "difid.mm"
include "syl.mm"
include "eqssd.mm"
include "istopon.mm"

theorem cctop
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( A e. V -> { x e. ~P A | ( ( A \ x ) ~<_ _om \/ x = (/) ) } e. ( TopOn ` A ) )

  proof
    cA
    cV
    wcel
    #
    cA
    vx
    cv
    #
    cdif
    #
    com
    cdom
    wbr
    #
    @1
    c0
    wceq
    #
    wo
    #
    vx
    cA
    cpw
    #
    crab
    #
    ctop
    wcel
    #
    cA
    @7
    cuni
    #
    wceq
    @7
    cA
    ctopon
    cfv
    wcel
    @0
    @8
    vy
    cv
    #
    @7
    wss
    #
    @10
    cuni
    #
    @7
    wcel
    #
    wi
    #
    vy
    wal
    #
    @10
    vz
    cv
    #
    cin
    #
    @7
    wcel
    #
    vz
    @7
    wral
    vy
    @7
    wral
    #
    wa
    #
    @15
    @19
    @14
    vy
    @11
    @12
    @6
    wcel
    #
    cA
    @12
    cdif
    #
    com
    cdom
    wbr
    #
    @12
    c0
    wceq
    #
    wo
    #
    @13
    @11
    @12
    cA
    wss
    @21
    @11
    @12
    @9
    cA
    @10
    @7
    uniss
    @7
    @6
    wss
    @9
    cA
    wss
    #
    @5
    vx
    @6
    ssrab2
    @7
    cA
    sspwuni
    mpbi
    #
    syl6ss
    @12
    cA
    vy
    vuniex
    elpw
    sylibr
    @11
    @23
    @24
    @11
    @24
    @23
    @24
    wn
    #
    @16
    c0
    wceq
    #
    wn
    #
    vz
    @10
    wrex
    #
    @11
    @23
    @28
    @29
    vz
    @10
    wral
    #
    wn
    @31
    @24
    @32
    vz
    @10
    uni0c
    notbii
    @29
    vz
    @10
    rexnal
    bitr4i
    @11
    @30
    @23
    vz
    @10
    @11
    @16
    @10
    wcel
    #
    @30
    @23
    @11
    @33
    wa
    #
    @30
    wa
    #
    cA
    @16
    cdif
    #
    com
    cdom
    wbr
    #
    @23
    @34
    @30
    @37
    @34
    @37
    @29
    @34
    @37
    @29
    @34
    @16
    @6
    wcel
    #
    @37
    @29
    wo
    #
    @34
    @16
    @7
    wcel
    #
    @38
    @39
    wa
    #
    @10
    @7
    @16
    ssel2
    @5
    @39
    vx
    @16
    @6
    @1
    @16
    wceq
    #
    @3
    @37
    @4
    @29
    @42
    @2
    @36
    com
    cdom
    @1
    @16
    cA
    difeq2
    breq1d
    @1
    @16
    c0
    eqeq1
    orbi12d
    elrab
    #
    sylib
    simprd
    ord
    con1d
    imp
    @35
    @37
    @22
    @36
    cdom
    wbr
    #
    @23
    @35
    @37
    wa
    #
    @36
    cvv
    wcel
    #
    @22
    @36
    wss
    #
    @44
    @37
    @46
    @35
    @36
    ctex
    adantl
    @45
    @33
    @16
    @12
    wss
    @47
    @11
    @33
    @30
    @37
    simpllr
    @16
    @10
    elssuni
    @16
    @12
    cA
    sscon
    3syl
    @22
    @36
    cvv
    ssdomg
    sylc
    @22
    @36
    com
    domtr
    sylancom
    mpdan
    exp31
    rexlimdv
    syl5bi
    con1d
    orrd
    @5
    @25
    vx
    @12
    @6
    @1
    @12
    wceq
    #
    @3
    @23
    @4
    @24
    @48
    @2
    @22
    com
    cdom
    @1
    @12
    cA
    difeq2
    breq1d
    @1
    @12
    c0
    eqeq1
    orbi12d
    elrab
    sylanbrc
    ax-gen
    @18
    vy
    vz
    @7
    @10
    @7
    wcel
    #
    @40
    wa
    @17
    @6
    wcel
    #
    cA
    @17
    cdif
    #
    com
    cdom
    wbr
    #
    @17
    c0
    wceq
    #
    wo
    #
    wa
    #
    @18
    @49
    @10
    @6
    wcel
    #
    cA
    @10
    cdif
    #
    com
    cdom
    wbr
    #
    @10
    c0
    wceq
    #
    wo
    #
    wa
    #
    @41
    @55
    @40
    @5
    @60
    vx
    @10
    @6
    @1
    @10
    wceq
    #
    @3
    @58
    @4
    @59
    @62
    @2
    @57
    com
    cdom
    @1
    @10
    cA
    difeq2
    breq1d
    @1
    @10
    c0
    eqeq1
    orbi12d
    elrab
    @43
    @61
    @41
    wa
    @50
    @54
    @56
    @50
    @60
    @41
    @10
    cA
    wss
    @17
    cA
    wss
    @56
    @50
    @10
    @16
    cA
    ssinss1
    @10
    cA
    vy
    vex
    #
    elpw
    @17
    cA
    @10
    @16
    @63
    inex1
    elpw
    3imtr4i
    ad2antrr
    @60
    @39
    @54
    @56
    @38
    @58
    @37
    @59
    @29
    @54
    @58
    @37
    wa
    #
    @52
    @53
    @64
    @51
    @57
    @36
    cun
    com
    cdom
    cA
    @10
    @16
    difindi
    @57
    @36
    unctb
    syl5eqbr
    orcd
    @59
    @53
    @52
    @59
    @17
    c0
    @16
    cin
    c0
    @10
    c0
    @16
    ineq1
    @16
    0in
    syl6eq
    olcd
    @29
    @53
    @52
    @29
    @17
    @10
    c0
    cin
    c0
    @16
    c0
    @10
    ineq2
    @10
    in0
    syl6eq
    olcd
    ccase2
    ad2ant2l
    jca
    syl2anb
    @5
    @54
    vx
    @17
    @6
    @1
    @17
    wceq
    #
    @3
    @52
    @4
    @53
    @65
    @2
    @51
    com
    cdom
    @1
    @17
    cA
    difeq2
    breq1d
    @1
    @17
    c0
    eqeq1
    orbi12d
    elrab
    sylibr
    rgen2a
    pm3.2i
    @0
    @6
    cvv
    wcel
    @7
    cvv
    wcel
    @8
    @20
    wb
    cA
    cV
    pwexg
    @5
    vx
    @6
    cvv
    rabexg
    vy
    vz
    cvv
    @7
    istopg
    3syl
    mpbiri
    @0
    cA
    @9
    @0
    cA
    @7
    wcel
    #
    cA
    @9
    wss
    @0
    cA
    @6
    wcel
    c0
    com
    cdom
    wbr
    #
    cA
    c0
    wceq
    #
    wo
    #
    @66
    cA
    cV
    pwidg
    @69
    @0
    @67
    @68
    com
    omex
    0dom
    orci
    a1i
    @5
    @69
    vx
    cA
    @6
    @1
    cA
    wceq
    #
    @3
    @67
    @4
    @68
    @70
    @2
    c0
    com
    cdom
    @70
    @2
    cA
    cA
    cdif
    c0
    @1
    cA
    cA
    difeq2
    cA
    difid
    syl6eq
    breq1d
    @1
    cA
    c0
    eqeq1
    orbi12d
    elrab
    sylanbrc
    cA
    @7
    elssuni
    syl
    @26
    @0
    @27
    a1i
    eqssd
    cA
    @7
    istopon
    sylanbrc
end
