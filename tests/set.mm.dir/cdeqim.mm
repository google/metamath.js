include "wi.mm"
include "wb.mm"
include "weq.mm"
include "cdeqri.mm"
include "imbi12d.mm"
include "cdeqi.mm"

theorem cdeqim
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  assume cdeqnot.1: |- CondEq ( x = y -> ( ph <-> ps ) )
  assume cdeqim.1: |- CondEq ( x = y -> ( ch <-> th ) )


  assert |- CondEq ( x = y -> ( ( ph -> ch ) <-> ( ps -> th ) ) )

  proof
    wph
    wch
    wi
    wps
    wth
    wi
    wb
    vx
    vy
    vx
    vy
    weq
    wph
    wps
    wch
    wth
    wph
    wps
    wb
    vx
    vy
    cdeqnot.1
    cdeqri
    wch
    wth
    wb
    vx
    vy
    cdeqim.1
    cdeqri
    imbi12d
    cdeqi
end
