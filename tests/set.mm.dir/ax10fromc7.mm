include "wal.mm"
include "wn.mm"
include "wi.mm"
include "ax-c4.mm"
include "ax-c5.mm"
include "id.mm"
include "mpg.mm"
include "nsyl.mm"
include "ax-c7.mm"
include "nsyl4.mm"

theorem ax10fromc7
  let wph: wff ph
  let vx: setvar x


  assert |- ( -. A. x ph -> A. x -. A. x ph )

  proof
    wph
    vx
    wal
    #
    vx
    wal
    #
    wn
    #
    vx
    wal
    #
    @0
    wn
    #
    vx
    wal
    #
    @0
    @3
    @4
    wi
    @3
    @5
    wi
    vx
    @2
    @4
    vx
    ax-c4
    @3
    @1
    @0
    @2
    vx
    ax-c5
    @0
    @0
    wi
    @0
    @1
    wi
    vx
    wph
    @0
    vx
    ax-c4
    @0
    id
    mpg
    nsyl
    mpg
    @0
    vx
    ax-c7
    nsyl4
end
