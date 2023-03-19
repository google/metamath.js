include "wal.mm"
include "ex.mm"
include "al2imi.mm"
include "imp.mm"

theorem alanimi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
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
