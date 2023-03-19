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
include "ineq2i.mm"
include "df-xrn.mm"
include "reseq1i.mm"
include "inres.mm"
include "eqtr4i.mm"
include "3eqtr4i.mm"

theorem xrnres2
  let cA: class A
  let cR: class R
  let cS: class S


  assert |- ( ( R |X. S ) |` A ) = ( R |X. ( S |` A ) )

  proof
    c1st
    cvv
    cvv
    cxp
    #
    cres
    ccnv
    cR
    ccom
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
    @2
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
    cR
    @6
    cxrn
    @4
    @7
    @1
    @2
    cS
    cA
    resco
    ineq2i
    @9
    @1
    @3
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
    @1
    @3
    cA
    inres
    eqtr4i
    cR
    @6
    df-xrn
    3eqtr4i
end
