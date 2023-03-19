include "cv.mm"
include "wceq.mm"
include "ccnv.mm"
include "cec.mm"
include "cin.mm"
include "c0.mm"
include "wo.mm"
include "wral.mm"
include "wbr.mm"
include "wrmo.mm"
include "wal.mm"
include "wrel.mm"
include "wb.mm"
include "relcnv.mm"
include "id.mm"
include "inecmo.mm"
include "ax-mp.mm"
include "cvv.mm"
include "brcnvg.mm"
include "el2v.mm"
include "rmobii.mm"
include "albii.mm"
include "bitri.mm"

theorem ineccnvmo
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cF: class F

  disjoint B x
  disjoint B y
  disjoint B z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F x
  disjoint F y
  disjoint F z
  assert |- ( A. y e. B A. z e. B ( y = z \/ ( [ y ] `' F i^i [ z ] `' F ) = (/) ) <-> A. x E* y e. B x F y )

  proof
    vy
    cv
    #
    vz
    cv
    #
    wceq
    #
    @0
    cF
    ccnv
    #
    cec
    @1
    @3
    cec
    cin
    c0
    wceq
    wo
    vz
    cB
    wral
    vy
    cB
    wral
    #
    @0
    vx
    cv
    #
    @3
    wbr
    #
    vy
    cB
    wrmo
    #
    vx
    wal
    #
    @5
    @0
    cF
    wbr
    #
    vy
    cB
    wrmo
    #
    vx
    wal
    @3
    wrel
    @4
    @8
    wb
    cF
    relcnv
    vy
    vz
    vx
    cB
    @0
    @1
    @3
    @2
    id
    inecmo
    ax-mp
    @7
    @10
    vx
    @6
    @9
    vy
    cB
    @6
    @9
    wb
    vy
    vx
    @0
    @5
    cvv
    cvv
    cF
    brcnvg
    el2v
    rmobii
    albii
    bitri
end
