include "wcel.mm"
include "wa.mm"
include "cv.mm"
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
include "ssrab.mm"
include "simprl.mm"
include "sspwuni.mm"
include "sylib.mm"
include "vuniex.mm"
include "elpw.mm"
include "sylibr.mm"
include "wn.mm"
include "wex.mm"
include "neq0.mm"
include "wrex.mm"
include "eluni2.mm"
include "r19.29.mm"
include "n0i.mm"
include "adantl.mm"
include "simpl.mm"
include "ord.mm"
include "mt3d.mm"
include "elunii.mm"
include "syl2anc.mm"
include "rexlimiva.mm"
include "syl.mm"
include "ex.mm"
include "ad2antll.mm"
include "syl5bi.mm"
include "exlimdv.mm"
include "con1d.mm"
include "orrd.mm"
include "eleq2.mm"
include "eqeq1.mm"
include "orbi12d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "alrimiv.mm"
include "anbi12i.mm"
include "inss1.mm"
include "simprll.mm"
include "elpwid.mm"
include "syl5ss.mm"
include "vex.mm"
include "inex1.mm"
include "ianor.mm"
include "elin.mm"
include "xchnxbir.mm"
include "simprlr.mm"
include "simprrr.mm"
include "orim12d.mm"
include "inss.mm"
include "ss0b.mm"
include "orbi12i.mm"
include "3imtr3i.mm"
include "syl6.mm"
include "ralrimivv.mm"
include "cvv.mm"
include "wb.mm"
include "pwexg.mm"
include "adantr.mm"
include "rabexg.mm"
include "istopg.mm"
include "mpbir2and.mm"
include "pwidg.mm"
include "simpr.mm"
include "orcd.mm"
include "elssuni.mm"
include "ssrab2.mm"
include "mpbi.mm"
include "a1i.mm"
include "eqssd.mm"
include "istopon.mm"

theorem ppttop
  let vx: setvar x
  let cA: class A
  let cP: class P
  let cV: class V
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint P x
  disjoint V x
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint P v
  disjoint P w
  disjoint P y
  disjoint P z
  disjoint V w
  disjoint V y
  disjoint V z
  assert |- ( ( A e. V /\ P e. A ) -> { x e. ~P A | ( P e. x \/ x = (/) ) } e. ( TopOn ` A ) )

  proof
    cA
    cV
    wcel
    #
    cP
    cA
    wcel
    #
    wa
    #
    cP
    vx
    cv
    #
    wcel
    #
    @3
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
    @8
    cuni
    #
    wceq
    @8
    cA
    ctopon
    cfv
    wcel
    @2
    @9
    vy
    cv
    #
    @8
    wss
    #
    @11
    cuni
    #
    @8
    wcel
    #
    wi
    #
    vy
    wal
    #
    @11
    vz
    cv
    #
    cin
    #
    @8
    wcel
    #
    vz
    @8
    wral
    vy
    @8
    wral
    #
    @2
    @15
    vy
    @12
    @11
    @7
    wss
    #
    @6
    vx
    @11
    wral
    #
    wa
    #
    @2
    @14
    @6
    vx
    @7
    @11
    ssrab
    @2
    @23
    @14
    @2
    @23
    wa
    #
    @13
    @7
    wcel
    #
    cP
    @13
    wcel
    #
    @13
    c0
    wceq
    #
    wo
    #
    @14
    @24
    @13
    cA
    wss
    #
    @25
    @24
    @21
    @29
    @2
    @21
    @22
    simprl
    @11
    cA
    sspwuni
    sylib
    @13
    cA
    vy
    vuniex
    elpw
    sylibr
    @24
    @26
    @27
    @24
    @27
    @26
    @27
    wn
    @17
    @13
    wcel
    #
    vz
    wex
    @24
    @26
    vz
    @13
    neq0
    @24
    @30
    @26
    vz
    @30
    @17
    @3
    wcel
    #
    vx
    @11
    wrex
    #
    @24
    @26
    vx
    @17
    @11
    eluni2
    @22
    @32
    @26
    wi
    @2
    @21
    @22
    @32
    @26
    @22
    @32
    wa
    @6
    @31
    wa
    #
    vx
    @11
    wrex
    @26
    @6
    @31
    vx
    @11
    r19.29
    @33
    @26
    vx
    @11
    @3
    @11
    wcel
    #
    @33
    wa
    @4
    @34
    @26
    @33
    @4
    @34
    @33
    @4
    @5
    @31
    @5
    wn
    @6
    @3
    @17
    n0i
    adantl
    @33
    @4
    @5
    @6
    @31
    simpl
    ord
    mt3d
    adantl
    @34
    @33
    simpl
    cP
    @3
    @11
    elunii
    syl2anc
    rexlimiva
    syl
    ex
    ad2antll
    syl5bi
    exlimdv
    syl5bi
    con1d
    orrd
    @6
    @28
    vx
    @13
    @7
    @3
    @13
    wceq
    @4
    @26
    @5
    @27
    @3
    @13
    cP
    eleq2
    @3
    @13
    c0
    eqeq1
    orbi12d
    elrab
    sylanbrc
    ex
    syl5bi
    alrimiv
    @2
    @19
    vy
    vz
    @8
    @8
    @11
    @8
    wcel
    #
    @17
    @8
    wcel
    #
    wa
    @11
    @7
    wcel
    #
    cP
    @11
    wcel
    #
    @11
    c0
    wceq
    #
    wo
    #
    wa
    #
    @17
    @7
    wcel
    #
    cP
    @17
    wcel
    #
    @17
    c0
    wceq
    #
    wo
    #
    wa
    #
    wa
    #
    @2
    @19
    @35
    @41
    @36
    @46
    @6
    @40
    vx
    @11
    @7
    @3
    @11
    wceq
    @4
    @38
    @5
    @39
    @3
    @11
    cP
    eleq2
    @3
    @11
    c0
    eqeq1
    orbi12d
    elrab
    @6
    @45
    vx
    @17
    @7
    @3
    @17
    wceq
    @4
    @43
    @5
    @44
    @3
    @17
    cP
    eleq2
    @3
    @17
    c0
    eqeq1
    orbi12d
    elrab
    anbi12i
    @2
    @47
    @19
    @2
    @47
    wa
    #
    @18
    @7
    wcel
    #
    cP
    @18
    wcel
    #
    @18
    c0
    wceq
    #
    wo
    #
    @19
    @48
    @18
    cA
    wss
    @49
    @48
    @18
    @11
    cA
    @11
    @17
    inss1
    @48
    @11
    cA
    @2
    @37
    @40
    @46
    simprll
    elpwid
    syl5ss
    @18
    cA
    @11
    @17
    vy
    vex
    inex1
    elpw
    sylibr
    @48
    @50
    @51
    @48
    @50
    wn
    #
    @39
    @44
    wo
    #
    @51
    @53
    @38
    wn
    #
    @43
    wn
    #
    wo
    #
    @48
    @54
    @38
    @43
    wa
    @57
    @50
    @38
    @43
    ianor
    cP
    @11
    @17
    elin
    xchnxbir
    @48
    @55
    @39
    @56
    @44
    @48
    @38
    @39
    @2
    @37
    @40
    @46
    simprlr
    ord
    @48
    @43
    @44
    @2
    @41
    @42
    @45
    simprrr
    ord
    orim12d
    syl5bi
    @11
    c0
    wss
    #
    @17
    c0
    wss
    #
    wo
    @18
    c0
    wss
    @54
    @51
    @11
    @17
    c0
    inss
    @58
    @39
    @59
    @44
    @11
    ss0b
    @17
    ss0b
    orbi12i
    @18
    ss0b
    3imtr3i
    syl6
    orrd
    @6
    @52
    vx
    @18
    @7
    @3
    @18
    wceq
    @4
    @50
    @5
    @51
    @3
    @18
    cP
    eleq2
    @3
    @18
    c0
    eqeq1
    orbi12d
    elrab
    sylanbrc
    ex
    syl5bi
    ralrimivv
    @2
    @8
    cvv
    wcel
    #
    @9
    @16
    @20
    wa
    wb
    @2
    @7
    cvv
    wcel
    #
    @60
    @0
    @61
    @1
    cA
    cV
    pwexg
    adantr
    @6
    vx
    @7
    cvv
    rabexg
    syl
    vy
    vz
    cvv
    @8
    istopg
    syl
    mpbir2and
    @2
    cA
    @10
    @2
    cA
    @8
    wcel
    #
    cA
    @10
    wss
    @2
    cA
    @7
    wcel
    #
    @1
    cA
    c0
    wceq
    #
    wo
    #
    @62
    @0
    @63
    @1
    cA
    cV
    pwidg
    adantr
    @2
    @1
    @64
    @0
    @1
    simpr
    orcd
    @6
    @65
    vx
    cA
    @7
    @3
    cA
    wceq
    @4
    @1
    @5
    @64
    @3
    cA
    cP
    eleq2
    @3
    cA
    c0
    eqeq1
    orbi12d
    elrab
    sylanbrc
    cA
    @8
    elssuni
    syl
    @10
    cA
    wss
    #
    @2
    @8
    @7
    wss
    @66
    @6
    vx
    @7
    ssrab2
    @8
    cA
    sspwuni
    mpbi
    a1i
    eqssd
    cA
    @8
    istopon
    sylanbrc
end
