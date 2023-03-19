include "weq.mm"
include "wal.mm"
include "wi.mm"
include "ax-c16.mm"
include "alrimiv.mm"
include "axc4i-o.mm"
include "equequ1.mm"
include "wb.mm"
include "cbvalv.mm"
include "a1i.mm"
include "imbi12d.mm"
include "albidv.mm"
include "biimpi.mm"
include "wex.mm"
include "nfa1-o.mm"
include "19.23.mm"
include "albii.mm"
include "ax6ev.mm"
include "pm2.27.mm"
include "ax-mp.mm"
include "alimi.mm"
include "equequ2.mm"
include "spv.mm"
include "sps-o.mm"
include "alcoms.mm"
include "syl.mm"
include "sylbi.mm"
include "3syl.mm"

theorem axc11n-16
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w

  disjoint x z
  disjoint w x
  disjoint w z
  assert |- ( A. x x = z -> A. z z = x )

  proof
    vx
    vz
    weq
    #
    vx
    wal
    #
    vx
    vw
    weq
    #
    @2
    vx
    wal
    #
    wi
    #
    vw
    wal
    #
    vx
    wal
    #
    vz
    vw
    weq
    #
    @7
    vz
    wal
    #
    wi
    #
    vw
    wal
    #
    vz
    wal
    #
    vz
    vx
    weq
    #
    vz
    wal
    @0
    @5
    vx
    @1
    @4
    vw
    @2
    vx
    vz
    ax-c16
    alrimiv
    axc4i-o
    @6
    @11
    @5
    @10
    vx
    vz
    @0
    @4
    @9
    vw
    @0
    @2
    @7
    @3
    @8
    vx
    vz
    vw
    equequ1
    #
    @3
    @8
    wb
    @0
    @2
    @7
    vx
    vz
    @13
    cbvalv
    a1i
    imbi12d
    albidv
    cbvalv
    biimpi
    @10
    @12
    vz
    @9
    @12
    vw
    vz
    @9
    vz
    wal
    #
    vw
    wal
    @7
    vz
    wex
    #
    @8
    wi
    #
    vw
    wal
    #
    @12
    @14
    @16
    vw
    @7
    @8
    vz
    @7
    vz
    nfa1-o
    19.23
    albii
    @17
    @8
    vw
    wal
    @12
    @16
    @8
    vw
    @15
    @16
    @8
    wi
    vz
    vw
    ax6ev
    @15
    @8
    pm2.27
    ax-mp
    alimi
    @7
    @12
    vz
    vw
    @7
    vw
    wal
    @12
    vz
    @7
    @12
    vw
    vx
    vw
    vx
    vz
    equequ2
    spv
    sps-o
    alcoms
    syl
    sylbi
    alcoms
    axc4i-o
    3syl
end
