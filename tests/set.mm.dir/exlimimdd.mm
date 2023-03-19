include "imp.mm"
include "exlimdd.mm"

theorem exlimimdd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume exlimimdd.1: |- F/ x ph
  assume exlimimdd.2: |- F/ x ch
  assume exlimimdd.3: |- ( ph -> E. x ps )
  assume exlimimdd.4: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ch )

  proof
    wph
    wps
    wch
    vx
    exlimimdd.1
    exlimimdd.2
    exlimimdd.3
    wph
    wps
    wch
    exlimimdd.4
    imp
    exlimdd
end
