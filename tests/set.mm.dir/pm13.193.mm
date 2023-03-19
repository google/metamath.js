include "weq.mm"
include "wsb.mm"
include "sbequ12.mm"
include "pm5.32ri.mm"

theorem pm13.193
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ph /\ x = y ) <-> ( [ y / x ] ph /\ x = y ) )

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
    sbequ12
    pm5.32ri
end
