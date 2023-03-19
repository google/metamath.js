include "wsb.mm"
include "wb.mm"
include "weq.mm"
include "sbequ12.mm"
include "bicomd.mm"
include "equcoms.mm"

theorem sbequ12r
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( x = y -> ( [ x / y ] ph <-> ph ) )

  proof
    wph
    vy
    vx
    wsb
    #
    wph
    wb
    vy
    vx
    vy
    vx
    weq
    wph
    @0
    wph
    vy
    vx
    sbequ12
    bicomd
    equcoms
end
