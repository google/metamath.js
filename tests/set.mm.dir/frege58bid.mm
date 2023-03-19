include "wal.mm"
include "wsb.mm"
include "ax-frege58b.mm"
include "sbid.mm"
include "biimpi.mm"
include "syl.mm"

theorem frege58bid
  let wph: wff ph
  let vx: setvar x


  assert |- ( A. x ph -> ph )

  proof
    wph
    vx
    wal
    wph
    vx
    vx
    wsb
    #
    wph
    wph
    vx
    vx
    ax-frege58b
    @0
    wph
    wph
    vx
    sbid
    biimpi
    syl
end
