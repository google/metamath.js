include "wex.mm"
include "wn.mm"
include "wal.mm"
include "df-ex.mm"
include "hbn1.mm"
include "hbxfrbi.mm"

theorem hbe1
  param wph: wff ph
  param vx: setvar x


  assert |- ( E. x ph -> A. x E. x ph )

  proof
    wph
    vx
    wex
    wph
    wn
    #
    vx
    wal
    wn
    vx
    wph
    vx
    df-ex
    @0
    vx
    hbn1
    hbxfrbi
end
