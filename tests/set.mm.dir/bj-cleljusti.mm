include "weq.mm"
include "wel.mm"
include "wa.mm"
include "ax8v1.mm"
include "imp.mm"
include "exlimiv.mm"

theorem bj-cleljusti
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x z
  disjoint y z
  assert |- ( E. z ( z = x /\ z e. y ) -> x e. y )

  proof
    vz
    vx
    weq
    #
    vz
    vy
    wel
    #
    wa
    vx
    vy
    wel
    #
    vz
    @0
    @1
    @2
    vz
    vx
    vy
    ax8v1
    imp
    exlimiv
end
