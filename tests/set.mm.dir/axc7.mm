include "wal.mm"
include "wn.mm"
include "sp.mm"
include "hbn1.mm"
include "nsyl4.mm"

theorem axc7
  let wph: wff ph
  let vx: setvar x


  assert |- ( -. A. x -. A. x ph -> ph )

  proof
    wph
    vx
    wal
    #
    wph
    @0
    wn
    vx
    wal
    wph
    vx
    sp
    wph
    vx
    hbn1
    nsyl4
end
