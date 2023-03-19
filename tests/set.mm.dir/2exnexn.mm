include "wn.mm"
include "wex.mm"
include "wal.mm"
include "alexn.mm"
include "con2bii.mm"

theorem 2exnexn
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( E. x A. y ph <-> -. A. x E. y -. ph )

  proof
    wph
    wn
    vy
    wex
    vx
    wal
    wph
    vy
    wal
    vx
    wex
    wph
    vx
    vy
    alexn
    con2bii
end
