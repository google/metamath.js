include "wal.mm"
include "wi.mm"
include "wn.mm"
include "hbnt.mm"
include "mpg.mm"

theorem hbn
  let wph: wff ph
  let vx: setvar x
  assume hbn.1: |- ( ph -> A. x ph )


  assert |- ( -. ph -> A. x -. ph )

  proof
    wph
    wph
    vx
    wal
    wi
    wph
    wn
    #
    @0
    vx
    wal
    wi
    vx
    wph
    vx
    hbnt
    hbn.1
    mpg
end
