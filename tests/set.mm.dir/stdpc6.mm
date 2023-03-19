include "weq.mm"
include "equid.mm"
include "ax-gen.mm"

theorem stdpc6
  let vx: setvar x


  assert |- A. x x = x

  proof
    vx
    vx
    weq
    vx
    vx
    equid
    ax-gen
end
