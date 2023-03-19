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
include "ineq2d.mm"
include "df-xrn.mm"
include "3eqtr4g.mm"

theorem xrneq2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> ( C |X. A ) = ( C |X. B ) )

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
    cC
    ccom
    #
    c2nd
    @1
    cres
    ccnv
    #
    cA
    ccom
    #
    cin
    @2
    @3
    cB
    ccom
    #
    cin
    cC
    cA
    cxrn
    cC
    cB
    cxrn
    @0
    @4
    @5
    @2
    cA
    cB
    @3
    coeq2
    ineq2d
    cC
    cA
    df-xrn
    cC
    cB
    df-xrn
    3eqtr4g
end
