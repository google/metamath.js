include "wsb.mm"
include "wal.mm"
include "2stdpc4.mm"
include "ax-gen.mm"
include "mpg.mm"
include "gen2.mm"

theorem pm11.11
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume pm11.11.1: |- ph


  assert |- A. z A. w [ z / x ] [ w / y ] ph

  proof
    wph
    vy
    vw
    wsb
    vx
    vz
    wsb
    #
    vz
    vw
    wph
    vy
    wal
    @0
    vx
    wph
    vx
    vy
    vz
    vw
    2stdpc4
    wph
    vy
    pm11.11.1
    ax-gen
    mpg
    gen2
end
