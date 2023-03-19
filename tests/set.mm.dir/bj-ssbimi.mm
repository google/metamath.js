include "wi.mm"
include "wssb.mm"
include "bj-ssbim.mm"
include "mpg.mm"

theorem bj-ssbimi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vt: setvar t
  assume bj-ssbimi.1: |- ( ph -> ps )


  assert |- ( [b t /b x ]b ph -> [b t /b x ]b ps )

  proof
    wph
    wps
    wi
    wph
    vx
    vt
    wssb
    wps
    vx
    vt
    wssb
    wi
    vx
    wph
    wps
    vx
    vt
    bj-ssbim
    bj-ssbimi.1
    mpg
end
