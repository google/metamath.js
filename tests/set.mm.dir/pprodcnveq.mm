include "cpprod.mm"
include "c1st.mm"
include "cvv.mm"
include "cxp.mm"
include "cres.mm"
include "ccnv.mm"
include "ccom.mm"
include "c2nd.mm"
include "cin.mm"
include "dfpprod2.mm"
include "cnveqi.mm"
include "cnvin.mm"
include "cnvco1.mm"
include "coeq1i.mm"
include "coass.mm"
include "3eqtri.mm"
include "ineq12i.mm"
include "eqtr4i.mm"

theorem pprodcnveq
  let cR: class R
  let cS: class S


  assert |- pprod ( R , S ) = `' pprod ( `' R , `' S )

  proof
    cR
    cS
    cpprod
    c1st
    cvv
    cvv
    cxp
    #
    cres
    #
    ccnv
    #
    cR
    @1
    ccom
    ccom
    #
    c2nd
    @0
    cres
    #
    ccnv
    #
    cS
    @4
    ccom
    ccom
    #
    cin
    #
    cR
    ccnv
    #
    cS
    ccnv
    #
    cpprod
    #
    ccnv
    #
    cR
    cS
    dfpprod2
    @11
    @2
    @8
    @1
    ccom
    #
    ccom
    #
    @5
    @9
    @4
    ccom
    #
    ccom
    #
    cin
    #
    ccnv
    @13
    ccnv
    #
    @15
    ccnv
    #
    cin
    @7
    @10
    @16
    @8
    @9
    dfpprod2
    cnveqi
    @13
    @15
    cnvin
    @17
    @3
    @18
    @6
    @17
    @12
    ccnv
    #
    @1
    ccom
    @2
    cR
    ccom
    #
    @1
    ccom
    @3
    @1
    @12
    cnvco1
    @19
    @20
    @1
    cR
    @1
    cnvco1
    coeq1i
    @2
    cR
    @1
    coass
    3eqtri
    @18
    @14
    ccnv
    #
    @4
    ccom
    @5
    cS
    ccom
    #
    @4
    ccom
    @6
    @4
    @14
    cnvco1
    @21
    @22
    @4
    cS
    @4
    cnvco1
    coeq1i
    @5
    cS
    @4
    coass
    3eqtri
    ineq12i
    3eqtri
    eqtr4i
end
