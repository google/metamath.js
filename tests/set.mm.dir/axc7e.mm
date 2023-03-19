include "wal.mm"
include "wex.mm"
include "hbe1a.mm"
include "sp.mm"
include "syl.mm"

theorem axc7e
  let wph: wff ph
  let vx: setvar x


  assert |- ( E. x A. x ph -> ph )

  proof
    wph
    vx
    wal
    #
    vx
    wex
    @0
    wph
    wph
    vx
    hbe1a
    wph
    vx
    sp
    syl
end
