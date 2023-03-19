include "wn.mm"
include "wal.mm"
include "axc7.mm"
include "con4i.mm"

theorem modal-b
  let wph: wff ph
  let vx: setvar x


  assert |- ( ph -> A. x -. A. x -. ph )

  proof
    wph
    wn
    #
    vx
    wal
    wn
    vx
    wal
    wph
    @0
    vx
    axc7
    con4i
end
