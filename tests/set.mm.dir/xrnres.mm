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
include "ineq1i.mm"
include "df-xrn.mm"
include "reseq1i.mm"
include "inres2.mm"
include "eqtr4i.mm"
include "3eqtr4i.mm"

theorem xrnres
  let cA: class A
  let cR: class R
  let cS: class S


  assert |- ( ( R |X. S ) |` A ) = ( ( R |` A ) |X. S )

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
    cS
    ccom
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
    cin
    cR
    cS
    cxrn
    #
    cA
    cres
    #
    @6
    cS
    cxrn
    @3
    @7
    @4
    @1
    cR
    cA
    resco
    ineq1i
    @9
    @2
    @4
    cin
    #
    cA
    cres
    @5
    @8
    @10
    cA
    cR
    cS
    df-xrn
    reseq1i
    cA
    @2
    @4
    inres2
    eqtr4i
    @6
    cS
    df-xrn
    3eqtr4i
end
