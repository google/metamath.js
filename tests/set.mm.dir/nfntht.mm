include "wex.mm"
include "wn.mm"
include "wal.mm"
include "wo.mm"
include "wnf.mm"
include "olc.mm"
include "nf2.mm"
include "sylibr.mm"

theorem nfntht
  let wph: wff ph
  let vx: setvar x


  assert |- ( -. E. x ph -> F/ x ph )

  proof
    wph
    vx
    wex
    wn
    #
    wph
    vx
    wal
    #
    @0
    wo
    wph
    vx
    wnf
    @0
    @1
    olc
    wph
    vx
    nf2
    sylibr
end
