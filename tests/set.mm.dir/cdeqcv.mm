include "weq.mm"
include "id.mm"
include "cdeqi.mm"

theorem cdeqcv
  let vx: setvar x
  let vy: setvar y


  assert |- CondEq ( x = y -> x = y )

  proof
    vx
    vy
    weq
    #
    vx
    vy
    @0
    id
    cdeqi
end
