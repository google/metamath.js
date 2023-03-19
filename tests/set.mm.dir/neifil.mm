include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cnei.mm"
include "cpw.mm"
include "wn.mm"
include "cv.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cin.mm"
include "cfil.mm"
include "wa.mm"
include "cuni.mm"
include "wceq.mm"
include "toponuni.mm"
include "adantr.mm"
include "ctop.mm"
include "topontop.mm"
include "simpr.mm"
include "sseqtrd.mm"
include "eqid.mm"
include "neiuni.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "eqimss2.mm"
include "syl.mm"
include "sspwuni.mm"
include "sylibr.mm"
include "3adant3.mm"
include "0nnei.mm"
include "sylan.mm"
include "3adant2.mm"
include "tpnei.mm"
include "biimpa.mm"
include "eqeltrd.mm"
include "3jca.mm"
include "elpwi.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "simprr.mm"
include "simplr.mm"
include "ssnei2.mm"
include "syl22anc.mm"
include "rexlimdvaa.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "innei.mm"
include "3expib.mm"
include "3ad2ant1.mm"
include "ralrimivv.mm"
include "isfil2.mm"
include "syl3anbrc.mm"

theorem neifil
  let cS: class S
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( J e. ( TopOn ` X ) /\ S C_ X /\ S =/= (/) ) -> ( ( nei ` J ) ` S ) e. ( Fil ` X ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cS
    cX
    wss
    #
    cS
    c0
    wne
    #
    w3a
    #
    cS
    cJ
    cnei
    cfv
    cfv
    #
    cX
    cpw
    #
    wss
    #
    c0
    @4
    wcel
    wn
    #
    cX
    @4
    wcel
    #
    w3a
    vy
    cv
    #
    vx
    cv
    #
    wss
    #
    vy
    @4
    wrex
    @10
    @4
    wcel
    #
    wi
    #
    vx
    @5
    wral
    #
    @10
    @9
    cin
    @4
    wcel
    #
    vy
    @4
    wral
    vx
    @4
    wral
    @4
    cX
    cfil
    cfv
    wcel
    @3
    @6
    @7
    @8
    @0
    @1
    @6
    @2
    @0
    @1
    wa
    #
    @4
    cuni
    #
    cX
    wss
    #
    @6
    @16
    cX
    @17
    wceq
    @18
    @16
    cX
    cJ
    cuni
    #
    @17
    @0
    cX
    @19
    wceq
    #
    @1
    cX
    cJ
    toponuni
    adantr
    #
    @16
    cJ
    ctop
    wcel
    #
    cS
    @19
    wss
    #
    @19
    @17
    wceq
    @0
    @22
    @1
    cX
    cJ
    topontop
    #
    adantr
    #
    @16
    cS
    cX
    @19
    @0
    @1
    simpr
    @21
    sseqtrd
    #
    cS
    cJ
    @19
    @19
    eqid
    #
    neiuni
    syl2anc
    eqtrd
    @17
    cX
    eqimss2
    syl
    @4
    cX
    sspwuni
    sylibr
    3adant3
    @0
    @2
    @7
    @1
    @0
    @22
    @2
    @7
    @24
    cS
    cJ
    0nnei
    sylan
    3adant2
    @0
    @1
    @8
    @2
    @16
    cX
    @19
    @4
    @21
    @16
    @22
    @23
    @19
    @4
    wcel
    #
    @25
    @26
    @22
    @23
    @28
    cS
    cJ
    @19
    @27
    tpnei
    biimpa
    syl2anc
    eqeltrd
    3adant3
    3jca
    @0
    @1
    @14
    @2
    @16
    @13
    vx
    @5
    @10
    @5
    wcel
    @16
    @10
    cX
    wss
    #
    @13
    @10
    cX
    elpwi
    @16
    @29
    wa
    #
    @11
    @12
    vy
    @4
    @30
    @9
    @4
    wcel
    #
    @11
    wa
    #
    wa
    #
    @22
    @31
    @11
    @10
    @19
    wss
    @12
    @16
    @22
    @29
    @32
    @25
    ad2antrr
    @30
    @31
    @11
    simprl
    @30
    @31
    @11
    simprr
    @33
    @10
    cX
    @19
    @16
    @29
    @32
    simplr
    @16
    @20
    @29
    @32
    @21
    ad2antrr
    sseqtrd
    cS
    cJ
    @10
    @9
    @19
    @27
    ssnei2
    syl22anc
    rexlimdvaa
    sylan2
    ralrimiva
    3adant3
    @3
    @15
    vx
    vy
    @4
    @4
    @0
    @1
    @12
    @31
    wa
    @15
    wi
    #
    @2
    @0
    @22
    @34
    @24
    @22
    @12
    @31
    @15
    cS
    cJ
    @9
    @10
    innei
    3expib
    syl
    3ad2ant1
    ralrimivv
    vx
    vy
    @4
    cX
    isfil2
    syl3anbrc
end
