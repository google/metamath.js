include "wal.mm"
include "wn.mm"
include "wo.mm"
include "wnf.mm"
include "notnot.mm"
include "alimi.mm"
include "orim1i.mm"
include "pm1.4.mm"
include "syl.mm"
include "nf3.mm"
include "3imtr4i.mm"

theorem nfntOLDOLD
  let wph: wff ph
  let vx: setvar x


  assert |- ( F/ x ph -> F/ x -. ph )

  proof
    wph
    vx
    wal
    #
    wph
    wn
    #
    vx
    wal
    #
    wo
    #
    @2
    @1
    wn
    #
    vx
    wal
    #
    wo
    #
    wph
    vx
    wnf
    @1
    vx
    wnf
    @3
    @5
    @2
    wo
    @6
    @0
    @5
    @2
    wph
    @4
    vx
    wph
    notnot
    alimi
    orim1i
    @5
    @2
    pm1.4
    syl
    wph
    vx
    nf3
    @1
    vx
    nf3
    3imtr4i
end
