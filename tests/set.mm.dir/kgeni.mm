include "ckgen.mm"
include "cfv.mm"
include "wcel.mm"
include "crest.mm"
include "co.mm"
include "ccmp.mm"
include "wa.mm"
include "cin.mm"
include "cuni.mm"
include "inass.mm"
include "in32.mm"
include "eqtr3i.mm"
include "wss.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "ctopon.mm"
include "ctop.mm"
include "cdm.mm"
include "crab.mm"
include "df-kgen.mm"
include "dmmptss.mm"
include "elfvdm.mm"
include "sseldi.mm"
include "adantr.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "simpl.mm"
include "elkgen.mm"
include "biimpa.mm"
include "syl2anc.mm"
include "simpld.mm"
include "df-ss.mm"
include "ineq1d.mm"
include "syl5eq.mm"
include "inss2.mm"
include "cvv.mm"
include "wb.mm"
include "cmptop.mm"
include "adantl.mm"
include "restrcl.mm"
include "simprd.mm"
include "syl.mm"
include "inex1g.mm"
include "elpwg.mm"
include "3syl.mm"
include "mpbiri.mm"
include "restin.mm"
include "simpr.mm"
include "eqeltrrd.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "ineq2.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "eleqtrrd.mm"

theorem kgeni
  let cA: class A
  let cJ: class J
  let cK: class K
  let vy: setvar y
  let vk: setvar k
  let vx: setvar x
  let vj: setvar j
  let cX: class X


  assert |- ( ( A e. ( kGen ` J ) /\ ( J |`t K ) e. Comp ) -> ( A i^i K ) e. ( J |`t K ) )

  proof
    cA
    cJ
    ckgen
    cfv
    wcel
    #
    cJ
    cK
    crest
    co
    #
    ccmp
    wcel
    #
    wa
    #
    cA
    cK
    cin
    #
    cJ
    cK
    cJ
    cuni
    #
    cin
    #
    crest
    co
    #
    @1
    @3
    cA
    @6
    cin
    #
    @4
    @7
    @3
    @8
    cA
    @5
    cin
    #
    cK
    cin
    #
    @4
    @4
    @5
    cin
    @8
    @10
    cA
    cK
    @5
    inass
    cA
    cK
    @5
    in32
    eqtr3i
    @3
    @9
    cA
    cK
    @3
    cA
    @5
    wss
    #
    @9
    cA
    wceq
    @3
    @11
    cJ
    vy
    cv
    #
    crest
    co
    #
    ccmp
    wcel
    #
    cA
    @12
    cin
    #
    @13
    wcel
    #
    wi
    #
    vy
    @5
    cpw
    #
    wral
    #
    @3
    cJ
    @5
    ctopon
    cfv
    wcel
    #
    @0
    @11
    @19
    wa
    #
    @3
    cJ
    ctop
    wcel
    #
    @20
    @0
    @22
    @2
    @0
    ckgen
    cdm
    ctop
    cJ
    vj
    ctop
    vj
    cv
    #
    @12
    crest
    co
    #
    ccmp
    wcel
    vx
    cv
    @12
    cin
    @24
    wcel
    wi
    vy
    @23
    cuni
    cpw
    #
    wral
    vx
    @25
    crab
    ckgen
    vx
    vj
    vy
    df-kgen
    dmmptss
    cA
    cJ
    ckgen
    elfvdm
    sseldi
    adantr
    #
    cJ
    @5
    @5
    eqid
    #
    toptopon
    sylib
    @0
    @2
    simpl
    @20
    @0
    @21
    cA
    vy
    cJ
    @5
    elkgen
    biimpa
    syl2anc
    #
    simpld
    cA
    @5
    df-ss
    sylib
    ineq1d
    syl5eq
    @3
    @6
    @18
    wcel
    #
    @19
    @7
    ccmp
    wcel
    #
    @8
    @7
    wcel
    #
    @3
    @29
    @6
    @5
    wss
    #
    cK
    @5
    inss2
    @3
    cK
    cvv
    wcel
    #
    @6
    cvv
    wcel
    @29
    @32
    wb
    @3
    @1
    ctop
    wcel
    #
    @33
    @2
    @34
    @0
    @1
    cmptop
    adantl
    @34
    cJ
    cvv
    wcel
    @33
    cK
    cJ
    restrcl
    simprd
    syl
    #
    cK
    @5
    cvv
    inex1g
    @6
    @5
    cvv
    elpwg
    3syl
    mpbiri
    @3
    @11
    @19
    @28
    simprd
    @3
    @1
    @7
    ccmp
    @3
    @22
    @33
    @1
    @7
    wceq
    @26
    @35
    cK
    cJ
    ctop
    cvv
    @5
    @27
    restin
    syl2anc
    #
    @0
    @2
    simpr
    eqeltrrd
    @17
    @30
    @31
    wi
    vy
    @6
    @18
    @12
    @6
    wceq
    #
    @14
    @30
    @16
    @31
    @37
    @13
    @7
    ccmp
    @12
    @6
    cJ
    crest
    oveq2
    #
    eleq1d
    @37
    @15
    @8
    @13
    @7
    @12
    @6
    cA
    ineq2
    @38
    eleq12d
    imbi12d
    rspcv
    syl3c
    eqeltrrd
    @36
    eleqtrrd
end
