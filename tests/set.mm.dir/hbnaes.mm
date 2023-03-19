include "weq.mm"
include "wal.mm"
include "wn.mm"
include "hbnae.mm"
include "syl.mm"

theorem hbnaes
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume hbnaes.1: |- ( A. z -. A. x x = y -> ph )


  assert |- ( -. A. x x = y -> ph )

  proof
    vx
    vy
    weq
    vx
    wal
    wn
    #
    @0
    vz
    wal
    wph
    vx
    vy
    vz
    hbnae
    hbnaes.1
    syl
end
