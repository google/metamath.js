include "wsb.mm"
include "weq.mm"
include "wb.mm"
include "sbequ12r.mm"
include "sps.mm"
include "dral1.mm"

theorem wl-ax11-lem5
  let wph: wff ph
  let vy: setvar y
  let vu: setvar u


  assert |- ( A. u u = y -> ( A. u [ u / y ] ph <-> A. y ph ) )

  proof
    wph
    vy
    vu
    wsb
    #
    wph
    vu
    vy
    vu
    vy
    weq
    @0
    wph
    wb
    vu
    wph
    vu
    vy
    sbequ12r
    sps
    dral1
end
