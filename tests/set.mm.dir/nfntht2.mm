include "wn.mm"
include "wal.mm"
include "wo.mm"
include "wnf.mm"
include "olc.mm"
include "nf3.mm"
include "sylibr.mm"

theorem nfntht2
  let wph: wff ph
  let vx: setvar x


  assert |- ( A. x -. ph -> F/ x ph )

  proof
    wph
    wn
    vx
    wal
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
    nf3
    sylibr
end
