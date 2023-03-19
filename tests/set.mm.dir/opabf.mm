include "copab.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "wal.mm"
include "gen2.mm"
include "opab0.mm"
include "mpbir.mm"

theorem opabf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume opabf.1: |- -. ph


  assert |- { <. x , y >. | ph } = (/)

  proof
    wph
    vx
    vy
    copab
    c0
    wceq
    wph
    wn
    #
    vy
    wal
    vx
    wal
    @0
    vx
    vy
    opabf.1
    gen2
    wph
    vx
    vy
    opab0
    mpbir
end
