include "weq.mm"
include "wssb.mm"
include "wi.mm"
include "equid.mm"
include "bj-ssbequ1.mm"
include "ax-mp.mm"

theorem bj-ssbid1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( ph -> [b x /b x ]b ph )

  proof
    vx
    vx
    weq
    wph
    wph
    vx
    vx
    wssb
    wi
    vx
    equid
    wph
    vx
    vx
    bj-ssbequ1
    ax-mp
end
