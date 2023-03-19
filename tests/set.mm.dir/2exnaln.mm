include "wex.mm"
include "wn.mm"
include "wal.mm"
include "df-ex.mm"
include "alnex.mm"
include "albii.mm"
include "xchbinxr.mm"

theorem 2exnaln
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( E. x E. y ph <-> -. A. x A. y -. ph )

  proof
    wph
    vy
    wex
    #
    vx
    wex
    @0
    wn
    #
    vx
    wal
    wph
    wn
    vy
    wal
    #
    vx
    wal
    @0
    vx
    df-ex
    @2
    @1
    vx
    wph
    vy
    alnex
    albii
    xchbinxr
end
