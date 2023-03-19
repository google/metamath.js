include "wrex.mm"
include "wn.mm"
include "wreu.mm"
include "wi.mm"
include "wrmo.mm"
include "pm2.21.mm"
include "rmo5.mm"
include "sylibr.mm"

theorem nrexrmo
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( -. E. x e. A ph -> E* x e. A ph )

  proof
    wph
    vx
    cA
    wrex
    #
    wn
    @0
    wph
    vx
    cA
    wreu
    #
    wi
    wph
    vx
    cA
    wrmo
    @0
    @1
    pm2.21
    wph
    vx
    cA
    rmo5
    sylibr
end
