include "c0.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "noel.mm"
include "pm2.21i.mm"
include "nrex.mm"

theorem rex0
  let wph: wff ph
  let vx: setvar x


  assert |- -. E. x e. (/) ph

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
    wn
    @0
    noel
    pm2.21i
    nrex
end
