include "wfal.mm"
include "wal.mm"
include "falim.mm"
include "sps.mm"

theorem unisym1
  let wph: wff ph
  let vx: setvar x


  assert |- ( A. x A. x F. -> A. x ph )

  proof
    wfal
    vx
    wal
    wph
    vx
    wal
    #
    vx
    wfal
    @0
    vx
    @0
    falim
    sps
    sps
end
