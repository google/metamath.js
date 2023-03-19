include "cres.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "copab.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "dfres2.mm"
include "inxprnres.mm"
include "eqtr4i.mm"

theorem dfres4
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( R |` A ) = ( R i^i ( A X. ran ( R |` A ) ) )

  proof
    cR
    cA
    cres
    #
    vx
    cv
    #
    cA
    wcel
    @1
    vy
    cv
    cR
    wbr
    wa
    vx
    vy
    copab
    cR
    cA
    @0
    crn
    cxp
    cin
    vx
    vy
    cA
    cR
    dfres2
    vx
    vy
    cA
    cR
    inxprnres
    eqtr4i
end
