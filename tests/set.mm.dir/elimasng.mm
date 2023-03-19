include "cv.mm"
include "csn.mm"
include "cima.mm"
include "wcel.mm"
include "cop.mm"
include "wb.mm"
include "wceq.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "eleq2d.mm"
include "opeq1.mm"
include "eleq1d.mm"
include "bibi12d.mm"
include "eleq1.mm"
include "opeq2.mm"
include "vex.mm"
include "elimasn.mm"
include "vtocl2g.mm"

theorem elimasng
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( B e. V /\ C e. W ) -> ( C e. ( A " { B } ) <-> <. B , C >. e. A ) )

  proof
    vz
    cv
    #
    cA
    vy
    cv
    #
    csn
    #
    cima
    #
    wcel
    #
    @1
    @0
    cop
    #
    cA
    wcel
    #
    wb
    @0
    cA
    cB
    csn
    #
    cima
    #
    wcel
    #
    cB
    @0
    cop
    #
    cA
    wcel
    #
    wb
    cC
    @8
    wcel
    #
    cB
    cC
    cop
    #
    cA
    wcel
    #
    wb
    vy
    vz
    cB
    cC
    cV
    cW
    @1
    cB
    wceq
    #
    @4
    @9
    @6
    @11
    @15
    @3
    @8
    @0
    @15
    @2
    @7
    cA
    @1
    cB
    sneq
    imaeq2d
    eleq2d
    @15
    @5
    @10
    cA
    @1
    cB
    @0
    opeq1
    eleq1d
    bibi12d
    @0
    cC
    wceq
    #
    @9
    @12
    @11
    @14
    @0
    cC
    @8
    eleq1
    @16
    @10
    @13
    cA
    @0
    cC
    cB
    opeq2
    eleq1d
    bibi12d
    cA
    @1
    @0
    vy
    vex
    vz
    vex
    elimasn
    vtocl2g
end
