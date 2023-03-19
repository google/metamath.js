include "wal.mm"
include "nf5rd.mm"
include "pm2.43i.mm"
include "nf5i.mm"

theorem nf5di
  let wph: wff ph
  let vx: setvar x
  assume nf5di.1: |- ( ph -> F/ x ph )


  assert |- F/ x ph

  proof
    wph
    vx
    wph
    wph
    vx
    wal
    wph
    wph
    vx
    nf5di.1
    nf5rd
    pm2.43i
    nf5i
end
