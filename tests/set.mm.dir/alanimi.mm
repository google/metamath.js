include "wal.mm"
include "ex.mm"
include "al2imi.mm"
include "imp.mm"

theorem alanimi
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param vx: setvar x
  assume alanimi.1: |- ( ( ph /\ ps ) -> ch )


  assert |- ( ( A. x ph /\ A. x ps ) -> A. x ch )

  proof
    wph
    vx
    wal
    wps
    vx
    wal
    wch
    vx
    wal
    wph
    wps
    wch
    vx
    wph
    wps
    wch
    alanimi.1
    ex
    al2imi
    imp
end
