include "wsb.mm"
include "wi.mm"
include "sbequ2.mm"
include "equcoms.mm"

theorem stdpc7
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( x = y -> ( [ x / y ] ph -> ph ) )

  proof
    wph
    vy
    vx
    wsb
    wph
    wi
    vy
    vx
    wph
    vy
    vx
    sbequ2
    equcoms
end
