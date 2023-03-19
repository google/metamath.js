include "cha.mm"
include "wcel.mm"
include "c1stc.mm"
include "wss.mm"
include "w3a.mm"
include "cpw.mm"
include "cdom.mm"
include "wbr.mm"
include "cn.mm"
include "wa.mm"
include "ccl.mm"
include "cfv.mm"
include "cmap.mm"
include "co.mm"
include "hausmapdom.mm"
include "adantr.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "simprr.mm"
include "c1.mm"
include "1nn.mm"
include "noel.mm"
include "eleq2.mm"
include "mtbiri.mm"
include "mt2.mm"
include "mapdom2.mm"
include "sylancl.mm"
include "c2o.mm"
include "csdm.mm"
include "cen.mm"
include "sdomdom.mm"
include "adantl.mm"
include "mapdom1.mm"
include "syl.mm"
include "cvv.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "ad2antll.mm"
include "pw2eng.mm"
include "ensym.mm"
include "3syl.mm"
include "domentr.mm"
include "syl2anc.mm"
include "cfn.mm"
include "wb.mm"
include "com.mm"
include "con0.mm"
include "cin.mm"
include "onfin2.mm"
include "inss2.mm"
include "eqsstri.mm"
include "2onn.mm"
include "sselii.mm"
include "simprl.mm"
include "brrelexi.mm"
include "fidomtri.mm"
include "sylancr.mm"
include "biimpar.mm"
include "ccrd.mm"
include "cdm.mm"
include "numth3.mm"
include "nnenom.mm"
include "ensymi.mm"
include "endomtr.mm"
include "simpr.mm"
include "mappwen.mm"
include "syl22anc.mm"
include "endom.mm"
include "syldan.mm"
include "pm2.61dan.mm"
include "domtr.mm"

theorem hauspwdom
  let cA: class A
  let cB: class B
  let cJ: class J
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  assume hauspwdom.1: |- X = U. J


  assert |- ( ( ( J e. Haus /\ J e. 1stc /\ A C_ X ) /\ ( A ~<_ ~P B /\ NN ~<_ B ) ) -> ( ( cls ` J ) ` A ) ~<_ ~P B )

  proof
    cJ
    cha
    wcel
    cJ
    c1stc
    wcel
    cA
    cX
    wss
    w3a
    #
    cA
    cB
    cpw
    #
    cdom
    wbr
    #
    cn
    cB
    cdom
    wbr
    #
    wa
    #
    wa
    #
    cA
    cJ
    ccl
    cfv
    cfv
    #
    cA
    cn
    cmap
    co
    #
    cdom
    wbr
    #
    @7
    @1
    cdom
    wbr
    #
    @6
    @1
    cdom
    wbr
    @0
    @8
    @4
    cA
    cJ
    cX
    hauspwdom.1
    hausmapdom
    adantr
    @5
    @7
    cA
    cB
    cmap
    co
    #
    cdom
    wbr
    #
    @10
    @1
    cdom
    wbr
    #
    @9
    @5
    @3
    cn
    c0
    wceq
    #
    cA
    c0
    wceq
    #
    wa
    #
    wn
    @11
    @0
    @2
    @3
    simprr
    #
    @15
    c1
    cn
    wcel
    #
    1nn
    @13
    @17
    wn
    @14
    @13
    @17
    c1
    c0
    wcel
    c1
    noel
    cn
    c0
    c1
    eleq2
    mtbiri
    adantr
    mt2
    cn
    cB
    cA
    mapdom2
    sylancl
    @5
    cA
    c2o
    csdm
    wbr
    #
    @12
    @5
    @18
    wa
    #
    @10
    c2o
    cB
    cmap
    co
    #
    cdom
    wbr
    #
    @20
    @1
    cen
    wbr
    #
    @12
    @19
    cA
    c2o
    cdom
    wbr
    #
    @21
    @18
    @23
    @5
    cA
    c2o
    sdomdom
    adantl
    cA
    c2o
    cB
    mapdom1
    syl
    @5
    @22
    @18
    @5
    cB
    cvv
    wcel
    #
    @1
    @20
    cen
    wbr
    @22
    @3
    @24
    @0
    @2
    cn
    cB
    cdom
    reldom
    brrelex2i
    ad2antll
    #
    cB
    cvv
    pw2eng
    @1
    @20
    ensym
    3syl
    adantr
    @10
    @20
    @1
    domentr
    syl2anc
    @5
    @18
    wn
    #
    c2o
    cA
    cdom
    wbr
    #
    @12
    @5
    @27
    @26
    @5
    c2o
    cfn
    wcel
    cA
    cvv
    wcel
    #
    @27
    @26
    wb
    com
    cfn
    c2o
    com
    con0
    cfn
    cin
    cfn
    onfin2
    con0
    cfn
    inss2
    eqsstri
    2onn
    sselii
    @5
    @2
    @28
    @0
    @2
    @3
    simprl
    #
    cA
    @1
    cdom
    reldom
    brrelexi
    syl
    c2o
    cA
    cvv
    fidomtri
    sylancr
    biimpar
    @5
    @27
    wa
    #
    @10
    @1
    cen
    wbr
    #
    @12
    @30
    cB
    ccrd
    cdm
    wcel
    #
    com
    cB
    cdom
    wbr
    #
    @27
    @2
    @31
    @5
    @32
    @27
    @5
    @24
    @32
    @25
    cB
    cvv
    numth3
    syl
    adantr
    @5
    @33
    @27
    @5
    com
    cn
    cen
    wbr
    @3
    @33
    cn
    com
    nnenom
    ensymi
    @16
    com
    cn
    cB
    endomtr
    sylancr
    adantr
    @5
    @27
    simpr
    @5
    @2
    @27
    @29
    adantr
    cA
    cB
    mappwen
    syl22anc
    @10
    @1
    endom
    syl
    syldan
    pm2.61dan
    @7
    @10
    @1
    domtr
    syl2anc
    @6
    @7
    @1
    domtr
    syl2anc
end
