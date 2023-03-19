include "wel.mm"
include "wn.mm"
include "ral0.mm"

theorem unt0
  let vx: setvar x


  assert |- A. x e. (/) -. x e. x

  proof
    vx
    vx
    wel
    wn
    vx
    ral0
end
