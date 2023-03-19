include "c1st.mm"
include "cvv.mm"
include "cxp.mm"
include "cres.mm"
include "ccnv.mm"
include "ccom.mm"
include "c2nd.mm"
include "cin.mm"
include "cxrn.mm"
include "resco.mm"
include "ineq12i.mm"
include "df-xrn.mm"
include "reseq1i.mm"
include "resindir.mm"
include "eqtri.mm"
include "3eqtr4i.mm"

theorem xrnres3
  let cA: class A
  let cR: class R
  let cS: class S


  assert |- ( ( R |X. S ) |` A ) = ( ( R |` A ) |X. ( S |` A ) )

  proof
    c1st
    cvv
    cvv
    cxp
    #
    cres
    ccnv
    #
    cR
    ccom
    #
    cA
    cres
    #
    c2nd
    @0
    cres
    ccnv
    #
    cS
    ccom
    #
    cA
    cres
    #
    cin
    #
    @1
    cR
    cA
    cres
    #
    ccom
    #
    @4
    cS
    cA
    cres
    #
    ccom
    #
    cin
    cR
    cS
    cxrn
    #
    cA
    cres
    #
    @8
    @10
    cxrn
    @3
    @9
    @6
    @11
    @1
    cR
    cA
    resco
    @4
    cS
    cA
    resco
    ineq12i
    @13
    @2
    @5
    cin
    #
    cA
    cres
    @7
    @12
    @14
    cA
    cR
    cS
    df-xrn
    reseq1i
    @2
    @5
    cA
    resindir
    eqtri
    @8
    @10
    df-xrn
    3eqtr4i
end
