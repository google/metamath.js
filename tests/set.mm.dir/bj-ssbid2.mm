include "weq.mm"
include "wssb.mm"
include "wi.mm"
include "equid.mm"
include "bj-ssbequ2.mm"
include "ax-mp.mm"

theorem bj-ssbid2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( [b x /b x ]b ph -> ph )

  proof
    vx
    vx
    weq
    wph
    vx
    vx
    wssb
    wph
    wi
    vx
    equid
    wph
    vx
    vx
    bj-ssbequ2
    ax-mp
end
