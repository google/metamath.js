include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "wa.mm"
include "cpw.mm"
include "cin.mm"
include "cvv.mm"
include "wss.mm"
include "cv.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wi.mm"
include "w3a.mm"
include "cfv.mm"
include "inex1g.mm"
include "adantr.mm"
include "inss2.mm"
include "a1i.mm"
include "simpr.mm"
include "pwidg.mm"
include "syl.mm"
include "elind.mm"
include "simpll.mm"
include "simplr.mm"
include "inss1.mm"
include "sseldi.mm"
include "difelsiga.mm"
include "syl3anc.mm"
include "difss.mm"
include "elpwg.mm"
include "mpbiri.mm"
include "ralrimiva.mm"
include "simplll.mm"
include "elpwi.mm"
include "sstr.mm"
include "mpan2.mm"
include "3syl.mm"
include "biimpar.mm"
include "syl2anc.mm"
include "sigaclcu.mm"
include "sspwuni.mm"
include "vuniex.mm"
include "elpw.mm"
include "bitr4i.mm"
include "sylib.mm"
include "ex.mm"
include "3jca.mm"
include "issiga.mm"
include "syl12anc.mm"

theorem sigainb
  let cA: class A
  let cS: class S
  let vx: setvar x


  assert |- ( ( S e. U. ran sigAlgebra /\ A e. S ) -> ( S i^i ~P A ) e. ( sigAlgebra ` A ) )

  proof
    cS
    csiga
    crn
    cuni
    #
    wcel
    #
    cA
    cS
    wcel
    #
    wa
    #
    cS
    cA
    cpw
    #
    cin
    #
    cvv
    wcel
    #
    @5
    @4
    wss
    #
    cA
    @5
    wcel
    #
    cA
    vx
    cv
    #
    cdif
    #
    @5
    wcel
    #
    vx
    @5
    wral
    #
    @9
    com
    cdom
    wbr
    #
    @9
    cuni
    #
    @5
    wcel
    #
    wi
    #
    vx
    @5
    cpw
    #
    wral
    #
    w3a
    #
    @5
    cA
    csiga
    cfv
    wcel
    #
    @1
    @6
    @2
    cS
    @4
    @0
    inex1g
    adantr
    @7
    @3
    cS
    @4
    inss2
    #
    a1i
    @3
    @8
    @12
    @18
    @3
    cS
    @4
    cA
    @1
    @2
    simpr
    #
    @3
    @2
    cA
    @4
    wcel
    @22
    cA
    cS
    pwidg
    syl
    elind
    @3
    @11
    vx
    @5
    @3
    @9
    @5
    wcel
    #
    wa
    #
    cS
    @4
    @10
    @24
    @1
    @2
    @9
    cS
    wcel
    @10
    cS
    wcel
    #
    @1
    @2
    @23
    simpll
    @1
    @2
    @23
    simplr
    @24
    @5
    cS
    @9
    cS
    @4
    inss1
    #
    @3
    @23
    simpr
    sseldi
    cA
    @9
    cS
    difelsiga
    syl3anc
    #
    @24
    @25
    @10
    @4
    wcel
    #
    @27
    @25
    @28
    @10
    cA
    wss
    cA
    @9
    difss
    @10
    cA
    cS
    elpwg
    mpbiri
    syl
    elind
    ralrimiva
    @3
    @16
    vx
    @17
    @3
    @9
    @17
    wcel
    #
    wa
    #
    @13
    @15
    @30
    @13
    wa
    #
    cS
    @4
    @14
    @31
    @1
    @9
    cS
    cpw
    wcel
    #
    @13
    @14
    cS
    wcel
    @1
    @2
    @29
    @13
    simplll
    @31
    @29
    @9
    cS
    wss
    #
    @32
    @3
    @29
    @13
    simplr
    #
    @31
    @29
    @9
    @5
    wss
    #
    @33
    @34
    @9
    @5
    elpwi
    #
    @35
    @5
    cS
    wss
    @33
    @26
    @9
    @5
    cS
    sstr
    mpan2
    3syl
    @29
    @32
    @33
    @9
    cS
    @17
    elpwg
    biimpar
    syl2anc
    @30
    @13
    simpr
    @9
    cS
    sigaclcu
    syl3anc
    @31
    @9
    @4
    wss
    #
    @14
    @4
    wcel
    #
    @31
    @29
    @35
    @37
    @34
    @36
    @35
    @7
    @37
    @21
    @9
    @5
    @4
    sstr
    mpan2
    3syl
    @37
    @14
    cA
    wss
    @38
    @9
    cA
    sspwuni
    @14
    cA
    vx
    vuniex
    elpw
    bitr4i
    sylib
    elind
    ex
    ralrimiva
    3jca
    @6
    @20
    @7
    @19
    wa
    vx
    @5
    cA
    issiga
    biimpar
    syl12anc
end
