include "weq.mm"
include "wsb.mm"
include "wb.mm"
include "sbequ.mm"
include "sps.mm"

theorem drsb2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A. x x = y -> ( [ x / z ] ph <-> [ y / z ] ph ) )

  proof
    vx
    vy
    weq
    wph
    vz
    vx
    wsb
    wph
    vz
    vy
    wsb
    wb
    vx
    wph
    vx
    vy
    vz
    sbequ
    sps
end
