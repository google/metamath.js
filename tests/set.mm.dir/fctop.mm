include "wcel.mm"
include "cv.mm"
include "cdif.mm"
include "cfn.mm"
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
include "eleq1d.mm"
include "eqeq1.mm"
include "orbi12d.mm"
include "elrab.mm"
include "sylib.mm"
include "simprd.mm"
include "ord.mm"
include "con1d.mm"
include "imp.mm"
include "elssuni.mm"
include "sscond.mm"
include "ssfi.mm"
include "sylan2.mm"
include "expcom.mm"
include "ad2antlr.mm"
include "mpd.mm"
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
include "unfi.mm"
include "syl5eqel.mm"
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
include "anbi12i.mm"
include "rgen2a.mm"
include "pm3.2i.mm"
include "cvv.mm"
include "wb.mm"
include "pwexg.mm"
include "rabexg.mm"
include "istopg.mm"
include "3syl.mm"
include "mpbiri.mm"
include "pwidg.mm"
include "0fin.mm"
include "orci.mm"
include "a1i.mm"
include "difid.mm"
include "syl.mm"
include "eqssd.mm"
include "istopon.mm"

theorem fctop
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
  assert |- ( A e. V -> { x e. ~P A | ( ( A \ x ) e. Fin \/ x = (/) ) } e. ( TopOn ` A ) )

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
    cfn
    wcel
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
    cfn
    wcel
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
    cA
    @16
    cdif
    #
    cfn
    wcel
    #
    @23
    @34
    @30
    @36
    @34
    @36
    @29
    @34
    @36
    @29
    @34
    @16
    @6
    wcel
    #
    @36
    @29
    wo
    #
    @34
    @16
    @7
    wcel
    #
    @37
    @38
    wa
    #
    @10
    @7
    @16
    ssel2
    @5
    @38
    vx
    @16
    @6
    @1
    @16
    wceq
    #
    @3
    @36
    @4
    @29
    @41
    @2
    @35
    cfn
    @1
    @16
    cA
    difeq2
    eleq1d
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
    @33
    @36
    @23
    wi
    @11
    @30
    @36
    @33
    @23
    @33
    @36
    @22
    @35
    wss
    @23
    @33
    @16
    @12
    cA
    @16
    @10
    elssuni
    sscond
    @35
    @22
    ssfi
    sylan2
    expcom
    ad2antlr
    mpd
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
    @43
    @2
    @22
    cfn
    @1
    @12
    cA
    difeq2
    eleq1d
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
    @6
    wcel
    #
    cA
    @10
    cdif
    #
    cfn
    wcel
    #
    @10
    c0
    wceq
    #
    wo
    #
    wa
    #
    @40
    wa
    #
    @17
    @6
    wcel
    #
    cA
    @17
    cdif
    #
    cfn
    wcel
    #
    @17
    c0
    wceq
    #
    wo
    #
    wa
    @10
    @7
    wcel
    #
    @39
    wa
    @18
    @50
    @51
    @55
    @44
    @51
    @48
    @40
    @10
    cA
    wss
    @17
    cA
    wss
    @44
    @51
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
    @57
    inex1
    elpw
    3imtr4i
    ad2antrr
    @48
    @38
    @55
    @44
    @37
    @46
    @36
    @47
    @29
    @55
    @46
    @36
    wa
    #
    @53
    @54
    @58
    @52
    @45
    @35
    cun
    cfn
    cA
    @10
    @16
    difindi
    @45
    @35
    unfi
    syl5eqel
    orcd
    @47
    @54
    @53
    @47
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
    @54
    @53
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
    @56
    @49
    @39
    @40
    @5
    @48
    vx
    @10
    @6
    @1
    @10
    wceq
    #
    @3
    @46
    @4
    @47
    @59
    @2
    @45
    cfn
    @1
    @10
    cA
    difeq2
    eleq1d
    @1
    @10
    c0
    eqeq1
    orbi12d
    elrab
    @42
    anbi12i
    @5
    @55
    vx
    @17
    @6
    @1
    @17
    wceq
    #
    @3
    @53
    @4
    @54
    @60
    @2
    @52
    cfn
    @1
    @17
    cA
    difeq2
    eleq1d
    @1
    @17
    c0
    eqeq1
    orbi12d
    elrab
    3imtr4i
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
    cfn
    wcel
    #
    cA
    c0
    wceq
    #
    wo
    #
    @61
    cA
    cV
    pwidg
    @64
    @0
    @62
    @63
    0fin
    orci
    a1i
    @5
    @64
    vx
    cA
    @6
    @1
    cA
    wceq
    #
    @3
    @62
    @4
    @63
    @65
    @2
    c0
    cfn
    @65
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
    eleq1d
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
