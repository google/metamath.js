include "wnf.mm"
include "wal.mm"
include "wi.mm"
include "nf5.mm"
include "nfa1.mm"
include "nfxfr.mm"

theorem nfnf1OLD
  let wph: wff ph
  let vx: setvar x


  assert |- F/ x F/ x ph

  proof
    wph
    vx
    wnf
    wph
    wph
    vx
    wal
    wi
    #
    vx
    wal
    vx
    wph
    vx
    nf5
    @0
    vx
    nfa1
    nfxfr
end
