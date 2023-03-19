include "wcel.mm"
include "cres.mm"
include "cec.mm"
include "cv.mm"
include "wbr.mm"
include "cab.mm"
include "wa.mm"
include "wb.mm"
include "cvv.mm"
include "elecres.mm"
include "elv.mm"
include "baib.mm"
include "abbi2dv.mm"
include "dfec2.mm"
include "eqtr4d.mm"

theorem ecres2
  let cA: class A
  let cB: class B
  let cR: class R
  let vy: setvar y


  assert |- ( B e. A -> [ B ] ( R |` A ) = [ B ] R )

  proof
    cB
    cA
    wcel
    #
    cB
    cR
    cA
    cres
    cec
    #
    cB
    vy
    cv
    #
    cR
    wbr
    #
    vy
    cab
    cB
    cR
    cec
    @0
    @3
    vy
    @1
    @2
    @1
    wcel
    #
    @0
    @3
    @4
    @0
    @3
    wa
    wb
    vy
    cA
    cB
    @2
    cR
    cvv
    elecres
    elv
    baib
    abbi2dv
    vy
    cB
    cR
    cA
    dfec2
    eqtr4d
end
