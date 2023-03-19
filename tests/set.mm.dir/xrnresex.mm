include "wcel.mm"
include "cres.mm"
include "w3a.mm"
include "cxrn.mm"
include "cvv.mm"
include "xrnres3.mm"
include "xrnres2.mm"
include "eqtr3i.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "dfres4.mm"
include "xrneq12i.mm"
include "simp1.mm"
include "resexg.mm"
include "rnexg.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "inxpxrn.mm"
include "xrninxpex.mm"
include "syl5eqel.mm"
include "syl3anc.mm"
include "syl5eqelr.mm"

theorem xrnresex
  let cA: class A
  let cR: class R
  let cS: class S
  let cV: class V
  let cW: class W
  let cX: class X


  assert |- ( ( A e. V /\ R e. W /\ ( S |` A ) e. X ) -> ( R |X. ( S |` A ) ) e. _V )

  proof
    cA
    cV
    wcel
    #
    cR
    cW
    wcel
    #
    cS
    cA
    cres
    #
    cX
    wcel
    #
    w3a
    #
    cR
    @2
    cxrn
    #
    cR
    cA
    cres
    #
    @2
    cxrn
    #
    cvv
    cR
    cS
    cxrn
    #
    cA
    cres
    @7
    @5
    cA
    cR
    cS
    xrnres3
    cA
    cR
    cS
    xrnres2
    eqtr3i
    @4
    @7
    cR
    cA
    @6
    crn
    #
    cxp
    cin
    #
    cS
    cA
    @2
    crn
    #
    cxp
    cin
    #
    cxrn
    #
    cvv
    @6
    @10
    @2
    @12
    cA
    cR
    dfres4
    cA
    cS
    dfres4
    xrneq12i
    @4
    @0
    @9
    cvv
    wcel
    #
    @11
    cvv
    wcel
    #
    @13
    cvv
    wcel
    @0
    @1
    @3
    simp1
    @1
    @0
    @14
    @3
    @1
    @6
    cvv
    wcel
    @14
    cR
    cA
    cW
    resexg
    @6
    cvv
    rnexg
    syl
    3ad2ant2
    @3
    @0
    @15
    @1
    @2
    cX
    rnexg
    3ad2ant3
    @0
    @14
    @15
    w3a
    @13
    @8
    cA
    @9
    @11
    cxp
    cxp
    cin
    cvv
    cA
    @9
    @11
    cR
    cS
    inxpxrn
    cA
    @9
    @11
    cR
    cS
    cV
    cvv
    cvv
    xrninxpex
    syl5eqel
    syl3anc
    syl5eqel
    syl5eqelr
end
