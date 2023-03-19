include "wal.mm"
include "wi.mm"
include "wnf.mm"
include "nf5-1.mm"
include "mpg.mm"

theorem nf5i
  let wph: wff ph
  let vx: setvar x
  assume nf5i.1: |- ( ph -> A. x ph )


  assert |- F/ x ph

  proof
    wph
    wph
    vx
    wal
    wi
    wph
    vx
    wnf
    vx
    wph
    vx
    nf5-1
    nf5i.1
    mpg
end
