include "wa.mm"
include "wal.mm"
include "19.26.mm"
include "19.3OLD.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem 19.27OLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume 19.27OLD.1: |- nfOLD x ps


  assert |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ ps ) )

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
    @0
    wps
    wa
    wph
    wps
    vx
    19.26
    @1
    wps
    @0
    wps
    vx
    19.27OLD.1
    19.3OLD
    anbi2i
    bitri
end
