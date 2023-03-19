include "cxrn.mm"
include "cres.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "xrnres3.mm"
include "dfres4.mm"
include "xrneq12i.mm"
include "inxpxrn.mm"
include "3eqtri.mm"

theorem xrnres4
  let cA: class A
  let cR: class R
  let cS: class S


  assert |- ( ( R |X. S ) |` A ) = ( ( R |X. S ) i^i ( A X. ( ran ( R |` A ) X. ran ( S |` A ) ) ) )

  proof
    cR
    cS
    cxrn
    #
    cA
    cres
    cR
    cA
    cres
    #
    cS
    cA
    cres
    #
    cxrn
    cR
    cA
    @1
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
    @0
    cA
    @3
    @5
    cxp
    cxp
    cin
    cA
    cR
    cS
    xrnres3
    @1
    @4
    @2
    @6
    cA
    cR
    dfres4
    cA
    cS
    dfres4
    xrneq12i
    cA
    @3
    @5
    cR
    cS
    inxpxrn
    3eqtri
end
