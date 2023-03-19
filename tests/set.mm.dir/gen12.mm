include "wal.mm"
include "in1.mm"
include "alrimivv.mm"
include "dfvd1ir.mm"

theorem gen12
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume gen12.1: |- (. ph ->. ps ).

  disjoint ph x
  disjoint ph y
  assert |- (. ph ->. A. x A. y ps ).

  proof
    wph
    wps
    vy
    wal
    vx
    wal
    wph
    wps
    vx
    vy
    wph
    wps
    gen12.1
    in1
    alrimivv
    dfvd1ir
end
