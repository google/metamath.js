include "wal.mm"
include "sp.mm"
include "nf5ri.mm"
include "impbii.mm"

theorem 19.3
  let wph: wff ph
  let vx: setvar x
  assume 19.3.1: |- F/ x ph


  assert |- ( A. x ph <-> ph )

  proof
    wph
    vx
    wal
    wph
    wph
    vx
    sp
    wph
    vx
    19.3.1
    nf5ri
    impbii
end
