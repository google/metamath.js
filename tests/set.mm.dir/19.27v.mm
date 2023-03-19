include "wa.mm"
include "wal.mm"
include "19.26.mm"
include "19.3v.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem 19.27v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x

  disjoint ps x
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
    19.3v
    anbi2i
    bitri
end
