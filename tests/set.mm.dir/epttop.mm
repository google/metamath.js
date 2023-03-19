include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "cpw.mm"
include "crab.mm"
include "ctop.mm"
include "cuni.mm"
include "ctopon.mm"
include "cfv.mm"
include "wss.mm"
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
include "wrex.mm"
include "eluni2.mm"
include "r19.29.mm"
include "simpr.mm"
include "impr.mm"
include "elssuni.mm"
include "adantr.mm"
include "eqsstr3d.mm"
include "rexlimiva.mm"
include "syl.mm"
include "ex.mm"
include "ad2antll.mm"
include "syl5bi.mm"
include "jctild.mm"
include "eqss.mm"
include "syl6ibr.mm"
include "eleq2.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "alrimiv.mm"
include "inss1.mm"
include "simprll.mm"
include "elpwid.mm"
include "syl5ss.mm"
include "vex.mm"
include "inex1.mm"
include "elin.mm"
include "simprlr.mm"
include "simprrr.mm"
include "anim12d.mm"
include "ineq12.mm"
include "inidm.mm"
include "syl6eq.mm"
include "syl6.mm"
include "jca.mm"
include "anbi12i.mm"
include "3imtr4g.mm"
include "ralrimivv.mm"
include "cvv.mm"
include "wb.mm"
include "pwexg.mm"
include "rabexg.mm"
include "istopg.mm"
include "mpbir2and.mm"
include "pwidg.mm"
include "eqidd.mm"
include "a1d.mm"
include "ssrab2.mm"
include "mpbi.mm"
include "a1i.mm"
include "eqssd.mm"
include "istopon.mm"

theorem epttop
  let vx: setvar x
  let cA: class A
  let cP: class P
  let cV: class V
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint P x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint P y
  disjoint P z
  disjoint V y
  disjoint V z
  assert |- ( ( A e. V /\ P e. A ) -> { x e. ~P A | ( P e. x -> x = A ) } e. ( TopOn ` A ) )

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
    cA
    wceq
    #
    wi
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
    cA
    wceq
    #
    wi
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
    #
    @13
    cA
    vy
    vuniex
    elpw
    sylibr
    @24
    @26
    @29
    cA
    @13
    wss
    #
    wa
    @27
    @24
    @26
    @31
    @29
    @26
    @4
    vx
    @11
    wrex
    #
    @24
    @31
    vx
    cP
    @11
    eluni2
    @22
    @32
    @31
    wi
    @2
    @21
    @22
    @32
    @31
    @22
    @32
    wa
    @6
    @4
    wa
    #
    vx
    @11
    wrex
    @31
    @6
    @4
    vx
    @11
    r19.29
    @33
    @31
    vx
    @11
    @3
    @11
    wcel
    #
    @33
    wa
    cA
    @3
    @13
    @34
    @6
    @4
    @5
    @34
    @6
    simpr
    impr
    @34
    @3
    @13
    wss
    @33
    @3
    @11
    elssuni
    adantr
    eqsstr3d
    rexlimiva
    syl
    ex
    ad2antll
    syl5bi
    @30
    jctild
    @13
    cA
    eqss
    syl6ibr
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
    cA
    eqeq1
    imbi12d
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
    @2
    @11
    @7
    wcel
    #
    cP
    @11
    wcel
    #
    @11
    cA
    wceq
    #
    wi
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
    cA
    wceq
    #
    wi
    #
    wa
    #
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
    cA
    wceq
    #
    wi
    #
    wa
    #
    @11
    @8
    wcel
    #
    @17
    @8
    wcel
    #
    wa
    @19
    @2
    @45
    @50
    @2
    @45
    wa
    #
    @46
    @49
    @53
    @18
    cA
    wss
    @46
    @53
    @18
    @11
    cA
    @11
    @17
    inss1
    @53
    @11
    cA
    @2
    @35
    @38
    @44
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
    @47
    @36
    @41
    wa
    #
    @53
    @48
    cP
    @11
    @17
    elin
    @53
    @54
    @37
    @42
    wa
    #
    @48
    @53
    @36
    @37
    @41
    @42
    @2
    @35
    @38
    @44
    simprlr
    @2
    @39
    @40
    @43
    simprrr
    anim12d
    @55
    @18
    cA
    cA
    cin
    cA
    @11
    cA
    @17
    cA
    ineq12
    cA
    inidm
    syl6eq
    syl6
    syl5bi
    jca
    ex
    @51
    @39
    @52
    @44
    @6
    @38
    vx
    @11
    @7
    @3
    @11
    wceq
    @4
    @36
    @5
    @37
    @3
    @11
    cP
    eleq2
    @3
    @11
    cA
    eqeq1
    imbi12d
    elrab
    @6
    @43
    vx
    @17
    @7
    @3
    @17
    wceq
    @4
    @41
    @5
    @42
    @3
    @17
    cP
    eleq2
    @3
    @17
    cA
    eqeq1
    imbi12d
    elrab
    anbi12i
    @6
    @49
    vx
    @18
    @7
    @3
    @18
    wceq
    @4
    @47
    @5
    @48
    @3
    @18
    cP
    eleq2
    @3
    @18
    cA
    eqeq1
    imbi12d
    elrab
    3imtr4g
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
    @56
    @0
    @57
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
    cA
    wceq
    #
    wi
    #
    @58
    @0
    @59
    @1
    cA
    cV
    pwidg
    adantr
    @2
    @60
    @1
    @2
    cA
    eqidd
    a1d
    @6
    @61
    vx
    cA
    @7
    @5
    @4
    @1
    @5
    @60
    @3
    cA
    cP
    eleq2
    @3
    cA
    cA
    eqeq1
    imbi12d
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
    @62
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
