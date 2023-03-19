include "wnf.mm"
include "wal.mm"
include "wi.mm"
include "nf5r.mm"
include "ax-mp.mm"

theorem nf5ri
  param wph: wff ph
  param vx: setvar x
  assume nf5ri.1: |- F/ x ph


  assert |- ( ph -> A. x ph )

  proof
    wph
    vx
    wnf
    wph
    wph
    vx
    wal
    wi
    nf5ri.1
    wph
    vx
    nf5r
    ax-mp
end
