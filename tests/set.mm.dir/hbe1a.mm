include "wal.mm"
include "wex.mm"
include "wn.mm"
include "df-ex.mm"
include "hbn1.mm"
include "con1i.mm"
include "sylbi.mm"

theorem hbe1a
  let wph: wff ph
  let vx: setvar x


  assert |- ( E. x A. x ph -> A. x ph )

  proof
    wph
    vx
    wal
    #
    vx
    wex
    @0
    wn
    vx
    wal
    #
    wn
    @0
    @0
    vx
    df-ex
    @0
    @1
    wph
    vx
    hbn1
    con1i
    sylbi
end
