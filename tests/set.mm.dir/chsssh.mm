include "cch.mm"
include "csh.mm"
include "cv.mm"
include "chsh.mm"
include "ssriv.mm"

theorem chsssh
  let vx: setvar x


  assert |- CH C_ SH

  proof
    vx
    cch
    csh
    vx
    cv
    chsh
    ssriv
end
