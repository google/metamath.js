include "wex.mm"
include "expcom.mm"
include "exlimd.mm"
include "mpan9.mm"

theorem exlimddvf
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  assume exlimddvf.1: |- ( ph -> E. x th )
  assume exlimddvf.2: |- F/ x ps
  assume exlimddvf.3: |- ( ( th /\ ps ) -> ch )
  assume exlimddvf.4: |- F/ x ch


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wth
    vx
    wex
    wps
    wch
    exlimddvf.1
    wps
    wth
    wch
    vx
    exlimddvf.2
    exlimddvf.4
    wth
    wps
    wch
    exlimddvf.3
    expcom
    exlimd
    mpan9
end
