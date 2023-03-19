include "wn.mm"
include "wb.mm"
include "weq.mm"
include "cdeqri.mm"
include "notbid.mm"
include "cdeqi.mm"

theorem cdeqnot
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume cdeqnot.1: |- CondEq ( x = y -> ( ph <-> ps ) )


  assert |- CondEq ( x = y -> ( -. ph <-> -. ps ) )

  proof
    wph
    wn
    wps
    wn
    wb
    vx
    vy
    vx
    vy
    weq
    wph
    wps
    wph
    wps
    wb
    vx
    vy
    cdeqnot.1
    cdeqri
    notbid
    cdeqi
end
