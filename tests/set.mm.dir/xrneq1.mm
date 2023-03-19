include "wceq.mm"
include "c1st.mm"
include "cvv.mm"
include "cxp.mm"
include "cres.mm"
include "ccnv.mm"
include "ccom.mm"
include "c2nd.mm"
include "cin.mm"
include "cxrn.mm"
include "coeq2.mm"
include "ineq1d.mm"
include "df-xrn.mm"
include "3eqtr4g.mm"

theorem xrneq1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> ( A |X. C ) = ( B |X. C ) )

  proof
    cA
    cB
    wceq
    #
    c1st
    cvv
    cvv
    cxp
    #
    cres
    ccnv
    #
    cA
    ccom
    #
    c2nd
    @1
    cres
    ccnv
    cC
    ccom
    #
    cin
    @2
    cB
    ccom
    #
    @4
    cin
    cA
    cC
    cxrn
    cB
    cC
    cxrn
    @0
    @3
    @5
    @4
    cA
    cB
    @2
    coeq2
    ineq1d
    cA
    cC
    df-xrn
    cB
    cC
    df-xrn
    3eqtr4g
end
