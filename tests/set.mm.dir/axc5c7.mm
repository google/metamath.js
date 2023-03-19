include "wal.mm"
include "wn.mm"
include "ax-c7.mm"
include "ax-c5.mm"
include "ja.mm"

theorem axc5c7
  let wph: wff ph
  let vx: setvar x


  assert |- ( ( A. x -. A. x ph -> A. x ph ) -> ph )

  proof
    wph
    vx
    wal
    #
    wn
    vx
    wal
    @0
    wph
    wph
    vx
    ax-c7
    wph
    vx
    ax-c5
    ja
end
