include "cv.mm"
include "cop.mm"
include "opex.mm"
include "moop2.mm"
include "euxfr2.mm"

theorem euop2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume euop2.1: |- A e. _V

  disjoint ph x
  disjoint A x
  disjoint x y
  assert |- ( E! x E. y ( x = <. A , y >. /\ ph ) <-> E! y ph )

  proof
    wph
    vx
    vy
    cA
    vy
    cv
    #
    cop
    cA
    @0
    opex
    vy
    vx
    cv
    cA
    euop2.1
    moop2
    euxfr2
end
