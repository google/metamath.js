include "cv.mm"
include "cima.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "imaexg.mm"
include "ax-mp.mm"
include "dfiin2.mm"

theorem intima0
  let vx: setvar x
  let cA: class A
  let cB: class B
  let va: setvar a

  disjoint A x
  disjoint B x
  disjoint a x
  assert |- |^|_ a e. A ( a " B ) = |^| { x | E. a e. A x = ( a " B ) }

  proof
    va
    vx
    cA
    va
    cv
    #
    cB
    cima
    #
    @0
    cvv
    wcel
    @1
    cvv
    wcel
    va
    vex
    @0
    cB
    cvv
    imaexg
    ax-mp
    dfiin2
end
