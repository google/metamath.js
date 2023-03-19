include "c0.mm"
include "cv.mm"
include "wcel.mm"
include "noel.mm"
include "pm2.21i.mm"
include "rgen.mm"

theorem ral0
  let wph: wff ph
  let vx: setvar x


  assert |- A. x e. (/) ph

  proof
    wph
    vx
    c0
    vx
    cv
    #
    c0
    wcel
    wph
    @0
    noel
    pm2.21i
    rgen
end
