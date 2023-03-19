include "wex.mm"
include "exlimdh.mm"
include "mpi.mm"

theorem eexinst01
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume eexinst01.1: |- E. x ps
  assume eexinst01.2: |- ( ph -> ( ps -> ch ) )
  assume eexinst01.3: |- ( ph -> A. x ph )
  assume eexinst01.4: |- ( ch -> A. x ch )


  assert |- ( ph -> ch )

  proof
    wph
    wps
    vx
    wex
    wch
    eexinst01.1
    wph
    wps
    wch
    vx
    eexinst01.3
    eexinst01.4
    eexinst01.2
    exlimdh
    mpi
end
