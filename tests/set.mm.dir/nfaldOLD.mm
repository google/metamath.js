include "wnf.mm"
include "wal.mm"
include "alrimi.mm"
include "nfnf1.mm"
include "nfal.mm"
include "hba1.mm"
include "sp.mm"
include "nf5rd.mm"
include "hbald.mm"
include "nf5d.mm"
include "syl.mm"

theorem nfaldOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume nfald.1: |- F/ y ph
  assume nfald.2: |- ( ph -> F/ x ps )


  assert |- ( ph -> F/ x A. y ps )

  proof
    wph
    wps
    vx
    wnf
    #
    vy
    wal
    #
    wps
    vy
    wal
    #
    vx
    wnf
    wph
    @0
    vy
    nfald.1
    nfald.2
    alrimi
    @1
    @2
    vx
    @0
    vx
    vy
    wps
    vx
    nfnf1
    nfal
    @1
    wps
    vx
    vy
    @0
    vy
    hba1
    @1
    wps
    vx
    @0
    vy
    sp
    nf5rd
    hbald
    nf5d
    syl
end
