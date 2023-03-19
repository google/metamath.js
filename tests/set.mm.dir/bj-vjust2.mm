include "wtru.mm"
include "cab.mm"
include "cv.mm"
include "wcel.mm"
include "wsb.mm"
include "df-clab.mm"
include "bj-sbfvv.mm"
include "3bitr4ri.mm"
include "bitri.mm"
include "eqriv.mm"

theorem bj-vjust2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- { x | T. } = { y | T. }

  proof
    vz
    wtru
    vx
    cab
    #
    wtru
    vy
    cab
    #
    vz
    cv
    #
    @0
    wcel
    wtru
    vx
    vz
    wsb
    #
    @2
    @1
    wcel
    #
    wtru
    vz
    vx
    df-clab
    wtru
    vy
    vz
    wsb
    wtru
    @4
    @3
    wtru
    vy
    vz
    bj-sbfvv
    wtru
    vz
    vy
    df-clab
    wtru
    vx
    vz
    bj-sbfvv
    3bitr4ri
    bitri
    eqriv
end
