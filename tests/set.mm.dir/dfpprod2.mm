include "cpprod.mm"
include "c1st.mm"
include "cvv.mm"
include "cxp.mm"
include "cres.mm"
include "ccom.mm"
include "c2nd.mm"
include "ctxp.mm"
include "ccnv.mm"
include "cin.mm"
include "df-pprod.mm"
include "df-txp.mm"
include "eqtri.mm"

theorem dfpprod2
  let cA: class A
  let cB: class B


  assert |- pprod ( A , B ) = ( ( `' ( 1st |` ( _V X. _V ) ) o. ( A o. ( 1st |` ( _V X. _V ) ) ) ) i^i ( `' ( 2nd |` ( _V X. _V ) ) o. ( B o. ( 2nd |` ( _V X. _V ) ) ) ) )

  proof
    cA
    cB
    cpprod
    cA
    c1st
    cvv
    cvv
    cxp
    #
    cres
    #
    ccom
    #
    cB
    c2nd
    @0
    cres
    #
    ccom
    #
    ctxp
    @1
    ccnv
    @2
    ccom
    @3
    ccnv
    @4
    ccom
    cin
    cA
    cB
    df-pprod
    @2
    @4
    df-txp
    eqtri
end
