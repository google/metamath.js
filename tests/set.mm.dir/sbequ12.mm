include "weq.mm"
include "wsb.mm"
include "sbequ1.mm"
include "sbequ2.mm"
include "impbid.mm"

theorem sbequ12
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( x = y -> ( ph <-> [ y / x ] ph ) )

  proof
    vx
    vy
    weq
    wph
    wph
    vx
    vy
    wsb
    wph
    vx
    vy
    sbequ1
    wph
    vx
    vy
    sbequ2
    impbid
end
