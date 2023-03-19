include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wel.mm"
include "wnf.mm"
include "wi.mm"
include "bj-axc14nf.mm"
include "nf5r.mm"
include "a1i.mm"
include "syld.mm"

theorem bj-axc14
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( -. A. z z = x -> ( -. A. z z = y -> ( x e. y -> A. z x e. y ) ) )

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
    vx
    vy
    wel
    #
    vz
    wnf
    #
    @1
    @1
    vz
    wal
    wi
    #
    vx
    vy
    vz
    bj-axc14nf
    @2
    @3
    wi
    @0
    @1
    vz
    nf5r
    a1i
    syld
end
