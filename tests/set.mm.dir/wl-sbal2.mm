include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wsb.mm"
include "wb.mm"
include "wl-naev.mm"
include "wl-sbalnae.mm"
include "mpdan.mm"

theorem wl-sbal2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x z
  assert |- ( -. A. x x = y -> ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) )

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
    vy
    vz
    vx
    wl-naev
    wph
    vx
    vy
    vz
    wl-sbalnae
    mpdan
end
