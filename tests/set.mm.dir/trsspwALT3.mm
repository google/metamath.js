include "wtr.mm"
include "cpw.mm"
include "cv.mm"
include "wcel.mm"
include "wss.mm"
include "trss.mm"
include "vex.mm"
include "elpw.mm"
include "syl6ibr.mm"
include "ssrdv.mm"

theorem trsspwALT3
  let cA: class A
  let vx: setvar x


  assert |- ( Tr A -> A C_ ~P A )

  proof
    cA
    wtr
    #
    vx
    cA
    cA
    cpw
    #
    @0
    vx
    cv
    #
    cA
    wcel
    @2
    cA
    wss
    @2
    @1
    wcel
    cA
    @2
    trss
    @2
    cA
    vx
    vex
    elpw
    syl6ibr
    ssrdv
end
