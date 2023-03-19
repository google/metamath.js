include "wex.mm"
include "eximdOLD.mm"
include "19.9OLD.mm"
include "syl6ib.mm"

theorem exlimdOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume exlimdOLD.1: |- nfOLD x ph
  assume exlimdOLD.2: |- nfOLD x ch
  assume exlimdOLD.3: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( E. x ps -> ch ) )

  proof
    wph
    wps
    vx
    wex
    wch
    vx
    wex
    wch
    wph
    wps
    wch
    vx
    exlimdOLD.1
    exlimdOLD.3
    eximdOLD
    wch
    vx
    exlimdOLD.2
    19.9OLD
    syl6ib
end
