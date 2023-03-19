include "clmod.mm"
include "cabl.mm"
include "cv.mm"
include "lmodabl.mm"
include "ssriv.mm"

theorem bj-modssabl
  let vx: setvar x


  assert |- LMod C_ Abel

  proof
    vx
    clmod
    cabl
    vx
    cv
    lmodabl
    ssriv
end
