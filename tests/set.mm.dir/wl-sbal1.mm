include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wsb.mm"
include "wb.mm"
include "wl-naev.mm"
include "wl-sbalnae.mm"
include "mpancom.mm"

theorem wl-sbal1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  assert |- ( -. A. x x = z -> ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) )

  proof
    vx
    vy
    weq
    vx
    wal
    wn
    vx
    vz
    weq
    vx
    wal
    wn
    wph
    vx
    wal
    vy
    vz
    wsb
    wph
    vy
    vz
    wsb
    vx
    wal
    wb
    vx
    vz
    vy
    vx
    wl-naev
    wph
    vx
    vy
    vz
    wl-sbalnae
    mpancom
end
