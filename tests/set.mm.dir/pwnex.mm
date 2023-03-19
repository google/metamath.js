include "cv.mm"
include "cpw.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wex.mm"
include "cab.mm"
include "wnel.mm"
include "wal.mm"
include "wn.mm"
include "abnex.mm"
include "df-nel.mm"
include "sylibr.mm"
include "vpwex.mm"
include "vex.mm"
include "pwid.mm"
include "pm3.2i.mm"
include "mpg.mm"

theorem pwnex
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- { x | E. y x = ~P y } e/ _V

  proof
    vy
    cv
    #
    cpw
    #
    cvv
    wcel
    #
    @0
    @1
    wcel
    #
    wa
    #
    vx
    cv
    @1
    wceq
    vy
    wex
    vx
    cab
    #
    cvv
    wnel
    #
    vy
    @4
    vy
    wal
    @5
    cvv
    wcel
    wn
    @6
    vy
    vx
    @1
    cvv
    abnex
    @5
    cvv
    df-nel
    sylibr
    @2
    @3
    vy
    vpwex
    @0
    vy
    vex
    pwid
    pm3.2i
    mpg
end
