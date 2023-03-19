include "wal.mm"
include "ax-gen.mm"

theorem gen2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume gen2.1: |- ph


  assert |- A. x A. y ph

  proof
    wph
    vy
    wal
    vx
    wph
    vy
    gen2.1
    ax-gen
    ax-gen
end
