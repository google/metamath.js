include "wn.mm"
include "wex.mm"
include "wal.mm"
include "df-ex.mm"
include "alex.mm"
include "albii.mm"
include "xchbinxr.mm"
include "bicomi.mm"

theorem 2nalexn
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( -. A. x A. y ph <-> E. x E. y -. ph )

  proof
    wph
    wn
    vy
    wex
    #
    vx
    wex
    #
    wph
    vy
    wal
    #
    vx
    wal
    #
    wn
    @1
    @0
    wn
    #
    vx
    wal
    @3
    @0
    vx
    df-ex
    @2
    @4
    vx
    wph
    vy
    alex
    albii
    xchbinxr
    bicomi
end
