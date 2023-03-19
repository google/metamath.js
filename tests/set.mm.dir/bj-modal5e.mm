include "wal.mm"
include "wex.mm"
include "wn.mm"
include "hbn1.mm"
include "alnex.mm"
include "sylib.mm"
include "con4i.mm"

theorem bj-modal5e
  let wph: wff ph
  let vx: setvar x


  assert |- ( E. x A. x ph -> A. x ph )

  proof
    wph
    vx
    wal
    #
    @0
    vx
    wex
    #
    @0
    wn
    #
    @2
    vx
    wal
    @1
    wn
    wph
    vx
    hbn1
    @0
    vx
    alnex
    sylib
    con4i
end
