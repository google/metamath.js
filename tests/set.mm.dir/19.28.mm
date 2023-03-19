include "wa.mm"
include "wal.mm"
include "19.26.mm"
include "19.3.mm"
include "anbi1i.mm"
include "bitri.mm"

theorem 19.28
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume 19.28.1: |- F/ x ph


  assert |- ( A. x ( ph /\ ps ) <-> ( ph /\ A. x ps ) )

  proof
    wph
    wps
    wa
    vx
    wal
    wph
    vx
    wal
    #
    wps
    vx
    wal
    #
    wa
    wph
    @1
    wa
    wph
    wps
    vx
    19.26
    @0
    wph
    @1
    wph
    vx
    19.28.1
    19.3
    anbi1i
    bitri
end
