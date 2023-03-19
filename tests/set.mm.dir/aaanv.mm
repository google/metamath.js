include "wa.mm"
include "wal.mm"
include "nfv.mm"
include "aaan.mm"
include "bicomi.mm"

theorem aaanv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y

  disjoint ph y
  disjoint ps x
  assert |- ( ( A. x ph /\ A. y ps ) <-> A. x A. y ( ph /\ ps ) )

  proof
    wph
    wps
    wa
    vy
    wal
    vx
    wal
    wph
    vx
    wal
    wps
    vy
    wal
    wa
    wph
    wps
    vx
    vy
    wph
    vy
    nfv
    wps
    vx
    nfv
    aaan
    bicomi
end
