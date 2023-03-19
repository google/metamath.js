include "cv.mm"
include "wbr.mm"
include "c-bnj14.mm"
include "breq1.mm"
include "df-bnj14.mm"
include "bnj1538.mm"
include "vtoclga.mm"

theorem bnj1418
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vz: setvar z


  assert |- ( y e. _pred ( x , A , R ) -> y R x )

  proof
    vz
    cv
    #
    vx
    cv
    #
    cR
    wbr
    #
    vy
    cv
    #
    @1
    cR
    wbr
    vz
    @3
    cA
    cR
    @1
    c-bnj14
    #
    @0
    @3
    @1
    cR
    breq1
    @2
    vz
    @4
    cA
    vz
    cA
    cR
    @1
    df-bnj14
    bnj1538
    vtoclga
end
