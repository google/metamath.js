include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "nfeqf.mm"
include "nf5rd.mm"
include "ex.mm"

theorem axc9
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( -. A. z z = x -> ( -. A. z z = y -> ( x = y -> A. z x = y ) ) )

  proof
    vz
    vx
    weq
    vz
    wal
    wn
    #
    vz
    vy
    weq
    vz
    wal
    wn
    #
    vx
    vy
    weq
    #
    @2
    vz
    wal
    wi
    @0
    @1
    wa
    @2
    vz
    vx
    vy
    vz
    nfeqf
    nf5rd
    ex
end
