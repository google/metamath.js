include "clocfin.mm"
include "cfv.mm"
include "wcel.mm"
include "cfn.mm"
include "cuni.mm"
include "wss.mm"
include "w3a.mm"
include "ctop.mm"
include "cun.mm"
include "wceq.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "crab.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "locfintop.mm"
include "ad2antrr.mm"
include "ssequn2.mm"
include "biimpi.mm"
include "adantl.mm"
include "eqid.mm"
include "locfinbas.mm"
include "uneq1d.mm"
include "eqtr3d.mm"
include "uniun.mm"
include "syl6eqr.mm"
include "locfinnei.mm"
include "adantlr.mm"
include "wi.mm"
include "simpr.mm"
include "rabfi.mm"
include "ad2antlr.mm"
include "rabun2.mm"
include "unfi.mm"
include "syl5eqel.mm"
include "syl2anc.mm"
include "ex.mm"
include "anim2d.mm"
include "reximdv.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "3jca.mm"
include "3impa.mm"
include "islocfin.mm"
include "sylibr.mm"

theorem lfinun
  let cA: class A
  let cB: class B
  let cJ: class J
  let vn: setvar n
  let vs: setvar s
  let vx: setvar x


  assert |- ( ( A e. ( LocFin ` J ) /\ B e. Fin /\ U. B C_ U. J ) -> ( A u. B ) e. ( LocFin ` J ) )

  proof
    cA
    cJ
    clocfin
    cfv
    #
    wcel
    #
    cB
    cfn
    wcel
    #
    cB
    cuni
    #
    cJ
    cuni
    #
    wss
    #
    w3a
    cJ
    ctop
    wcel
    #
    @4
    cA
    cB
    cun
    #
    cuni
    #
    wceq
    #
    vx
    cv
    #
    vn
    cv
    #
    wcel
    #
    vs
    cv
    @11
    cin
    c0
    wne
    #
    vs
    @7
    crab
    #
    cfn
    wcel
    #
    wa
    #
    vn
    cJ
    wrex
    #
    vx
    @4
    wral
    #
    w3a
    #
    @7
    @0
    wcel
    @1
    @2
    @5
    @19
    @1
    @2
    wa
    #
    @5
    wa
    #
    @6
    @9
    @18
    @1
    @6
    @2
    @5
    cA
    cJ
    locfintop
    ad2antrr
    @21
    @4
    cA
    cuni
    #
    @3
    cun
    #
    @8
    @21
    @4
    @3
    cun
    #
    @4
    @23
    @5
    @24
    @4
    wceq
    #
    @20
    @5
    @25
    @3
    @4
    ssequn2
    biimpi
    adantl
    @21
    @4
    @22
    @3
    @1
    @4
    @22
    wceq
    @2
    @5
    cA
    cJ
    @4
    @22
    @4
    eqid
    #
    @22
    eqid
    locfinbas
    ad2antrr
    uneq1d
    eqtr3d
    cA
    cB
    uniun
    syl6eqr
    @21
    @17
    vx
    @4
    @21
    @10
    @4
    wcel
    #
    wa
    #
    @12
    @13
    vs
    cA
    crab
    #
    cfn
    wcel
    #
    wa
    #
    vn
    cJ
    wrex
    #
    @17
    @20
    @27
    @32
    @5
    @1
    @27
    @32
    @2
    cA
    @10
    vn
    cJ
    @4
    vs
    @26
    locfinnei
    adantlr
    adantlr
    @28
    @31
    @16
    vn
    cJ
    @28
    @30
    @15
    @12
    @20
    @30
    @15
    wi
    @5
    @27
    @20
    @30
    @15
    @20
    @30
    wa
    @30
    @13
    vs
    cB
    crab
    #
    cfn
    wcel
    #
    @15
    @20
    @30
    simpr
    @2
    @34
    @1
    @30
    @13
    vs
    cB
    rabfi
    ad2antlr
    @30
    @34
    wa
    @14
    @29
    @33
    cun
    cfn
    @13
    vs
    cA
    cB
    rabun2
    @29
    @33
    unfi
    syl5eqel
    syl2anc
    ex
    ad2antrr
    anim2d
    reximdv
    mpd
    ralrimiva
    3jca
    3impa
    vx
    @7
    vn
    cJ
    @4
    @8
    vs
    @26
    @8
    eqid
    islocfin
    sylibr
end
