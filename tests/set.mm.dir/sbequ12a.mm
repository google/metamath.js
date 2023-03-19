include "weq.mm"
include "wsb.mm"
include "sbequ12r.mm"
include "sbequ12.mm"
include "bitr2d.mm"

theorem sbequ12a
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( x = y -> ( [ y / x ] ph <-> [ x / y ] ph ) )

  proof
    vx
    vy
    weq
    wph
    vy
    vx
    wsb
    wph
    wph
    vx
    vy
    wsb
    wph
    vx
    vy
    sbequ12r
    wph
    vx
    vy
    sbequ12
    bitr2d
end
