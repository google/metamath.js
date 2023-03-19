include "wal.mm"
include "sp.mm"
include "nfriOLD.mm"
include "impbii.mm"

theorem 19.3OLD
  let wph: wff ph
  let vx: setvar x
  assume 19.3OLD.1: |- nfOLD x ph


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
    19.3OLD.1
    nfriOLD
    impbii
end
