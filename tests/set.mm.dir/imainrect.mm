include "cxp.mm"
include "cin.mm"
include "cres.mm"
include "crn.mm"
include "cvv.mm"
include "cima.mm"
include "df-res.mm"
include "rneqi.mm"
include "df-ima.mm"
include "eqtri.mm"
include "ineq1i.mm"
include "ccnv.mm"
include "cdm.mm"
include "cnvin.mm"
include "inxp.mm"
include "inv1.mm"
include "incom.mm"
include "xpeq12i.mm"
include "eqtr2i.mm"
include "ineq2i.mm"
include "in32.mm"
include "xpindir.mm"
include "inass.mm"
include "eqtr4i.mm"
include "3eqtr4i.mm"
include "cnveqi.mm"
include "cnvxp.mm"
include "3eqtr4ri.mm"
include "dmeqi.mm"
include "dmres.mm"
include "df-rn.mm"

theorem imainrect
  let cA: class A
  let cB: class B
  let cG: class G
  let cY: class Y


  assert |- ( ( G i^i ( A X. B ) ) " Y ) = ( ( G " ( Y i^i A ) ) i^i B )

  proof
    cG
    cA
    cB
    cxp
    #
    cin
    #
    cY
    cres
    #
    crn
    @1
    cY
    cvv
    cxp
    #
    cin
    #
    crn
    #
    @1
    cY
    cima
    cG
    cY
    cA
    cin
    #
    cima
    #
    cB
    cin
    #
    @2
    @4
    @1
    cY
    df-res
    rneqi
    @1
    cY
    df-ima
    @8
    cG
    @6
    cvv
    cxp
    #
    cin
    #
    crn
    #
    cB
    cin
    #
    @5
    @7
    @11
    cB
    @7
    cG
    @6
    cres
    #
    crn
    @11
    cG
    @6
    df-ima
    @13
    @10
    cG
    @6
    df-res
    rneqi
    eqtri
    ineq1i
    @10
    ccnv
    #
    cB
    cres
    #
    cdm
    #
    @4
    ccnv
    #
    cdm
    @12
    @5
    @15
    @17
    @10
    cvv
    cB
    cxp
    #
    cin
    #
    ccnv
    @14
    @18
    ccnv
    #
    cin
    #
    @17
    @15
    @10
    @18
    cnvin
    @4
    @19
    cG
    @3
    cin
    #
    @0
    cin
    @22
    cA
    cvv
    cxp
    #
    @18
    cin
    #
    cin
    #
    @4
    @19
    @0
    @24
    @22
    @24
    cA
    cvv
    cin
    #
    cvv
    cB
    cin
    #
    cxp
    @0
    cA
    cvv
    cvv
    cB
    inxp
    @26
    cA
    @27
    cB
    cA
    inv1
    @27
    cB
    cvv
    cin
    cB
    cvv
    cB
    incom
    cB
    inv1
    eqtri
    xpeq12i
    eqtr2i
    ineq2i
    cG
    @0
    @3
    in32
    @19
    @22
    @23
    cin
    #
    @18
    cin
    @25
    @10
    @28
    @18
    @10
    cG
    @3
    @23
    cin
    #
    cin
    @28
    @9
    @29
    cG
    cY
    cA
    cvv
    xpindir
    ineq2i
    cG
    @3
    @23
    inass
    eqtr4i
    ineq1i
    @22
    @23
    @18
    inass
    eqtri
    3eqtr4i
    cnveqi
    @15
    @14
    cB
    cvv
    cxp
    #
    cin
    @21
    @14
    cB
    df-res
    @20
    @30
    @14
    cvv
    cB
    cnvxp
    ineq2i
    eqtr4i
    3eqtr4ri
    dmeqi
    cB
    @14
    cdm
    #
    cin
    @31
    cB
    cin
    @16
    @12
    cB
    @31
    incom
    @14
    cB
    dmres
    @11
    @31
    cB
    @10
    df-rn
    ineq1i
    3eqtr4ri
    @4
    df-rn
    3eqtr4ri
    eqtr4i
    3eqtr4i
end
