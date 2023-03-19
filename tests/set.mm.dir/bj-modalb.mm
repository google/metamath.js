include "wal.mm"
include "wn.mm"
include "axc7.mm"
include "con1i.mm"

theorem bj-modalb
  let wph: wff ph
  let vx: setvar x


  assert |- ( -. ph -> A. x -. A. x ph )

  proof
    wph
    vx
    wal
    wn
    vx
    wal
    wph
    wph
    vx
    axc7
    con1i
end
