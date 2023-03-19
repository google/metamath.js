include "cv.mm"
include "ax-frege54c.mm"

theorem frege54b
  let vx: setvar x


  assert |- x = x

  proof
    vx
    cv
    ax-frege54c
end
