include "weq.mm"
include "wal.mm"
include "wb.mm"
include "wa.mm"
include "sp.mm"
include "equequ2.mm"
include "alimi.mm"
include "albi.mm"
include "syl.mm"
include "jca.mm"
include "wi.mm"
include "ax7.mm"
include "al2imi.mm"
include "a1dd.mm"
include "axc9.mm"
include "bija.mm"
include "impcom.mm"
include "impbii.mm"

theorem wl-aleq
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A. x y = z <-> ( y = z /\ ( A. x x = y <-> A. x x = z ) ) )

  proof
    vy
    vz
    weq
    #
    vx
    wal
    #
    @0
    vx
    vy
    weq
    #
    vx
    wal
    #
    vx
    vz
    weq
    #
    vx
    wal
    #
    wb
    #
    wa
    @1
    @0
    @6
    @0
    vx
    sp
    @1
    @2
    @4
    wb
    #
    vx
    wal
    @6
    @0
    @7
    vx
    vy
    vz
    vx
    equequ2
    alimi
    @2
    @4
    vx
    albi
    syl
    jca
    @6
    @0
    @1
    @3
    @5
    @0
    @1
    wi
    @3
    @5
    @1
    @0
    @2
    @4
    @0
    vx
    vx
    vy
    vz
    ax7
    al2imi
    a1dd
    vy
    vz
    vx
    axc9
    bija
    impcom
    impbii
end
