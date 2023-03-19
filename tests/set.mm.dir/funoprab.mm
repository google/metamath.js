include "wmo.mm"
include "wal.mm"
include "coprab.mm"
include "wfun.mm"
include "gen2.mm"
include "funoprabg.mm"
include "ax-mp.mm"

theorem funoprab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume funoprab.1: |- E* z ph

  disjoint x y
  disjoint x z
  disjoint y z
  assert |- Fun { <. <. x , y >. , z >. | ph }

  proof
    wph
    vz
    wmo
    #
    vy
    wal
    vx
    wal
    wph
    vx
    vy
    vz
    coprab
    wfun
    @0
    vx
    vy
    funoprab.1
    gen2
    wph
    vx
    vy
    vz
    funoprabg
    ax-mp
end
