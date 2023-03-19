include "wa.mm"
include "wal.mm"
include "19.26.mm"
include "19.3v.mm"
include "anbi1i.mm"
include "bitri.mm"

theorem 19.28v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x

  disjoint ph x
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
    19.3v
    anbi1i
    bitri
end
