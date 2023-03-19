include "cv.mm"
include "wceq.mm"
include "wal.mm"
include "wi.mm"
include "id.mm"
include "2th.mm"

theorem trujust
  let vx.tru: setvar x
  let vy.tru: setvar y


  assert |- ( ( A. x x = x -> A. x x = x ) <-> ( A. y y = y -> A. y y = y ) )

  proof
    vx.tru
    cv
    #
    @0
    wceq
    vx.tru
    wal
    #
    @1
    wi
    vy.tru
    cv
    #
    @2
    wceq
    vy.tru
    wal
    #
    @3
    wi
    @1
    id
    @3
    id
    2th
end
