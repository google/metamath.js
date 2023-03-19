include "wn.mm"
include "wal.mm"
include "wex.mm"
include "2exnaln.mm"
include "bicomi.mm"
include "con1bii.mm"

theorem 2nexaln
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( -. E. x E. y ph <-> A. x A. y -. ph )

  proof
    wph
    wn
    vy
    wal
    vx
    wal
    #
    wph
    vy
    wex
    vx
    wex
    #
    @1
    @0
    wn
    wph
    vx
    vy
    2exnaln
    bicomi
    con1bii
end
