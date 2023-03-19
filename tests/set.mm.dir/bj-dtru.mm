include "weq.mm"
include "wn.mm"
include "wex.mm"
include "wal.mm"
include "wel.mm"
include "wa.mm"
include "bj-el.mm"
include "ax-nul.mm"
include "sp.mm"
include "eximii.mm"
include "eeanv.mm"
include "mpbir2an.mm"
include "ax9.mm"
include "com12.mm"
include "con3dimp.mm"
include "2eximi.mm"
include "ax-mp.mm"
include "wi.mm"
include "equequ2.mm"
include "notbid.mm"
include "ax7.mm"
include "con3d.mm"
include "bj-spimevv.mm"
include "syl6bi.mm"
include "a1d.mm"
include "pm2.61i.mm"
include "exlimivv.mm"
include "exnal.mm"
include "mpbi.mm"

theorem bj-dtru
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z

  disjoint x y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  assert |- -. A. x x = y

  proof
    vx
    vy
    weq
    #
    wn
    #
    vx
    wex
    #
    @0
    vx
    wal
    wn
    vw
    vz
    weq
    #
    wn
    #
    vz
    wex
    vw
    wex
    #
    @2
    vx
    vw
    wel
    #
    vx
    vz
    wel
    #
    wn
    #
    wa
    #
    vz
    wex
    vw
    wex
    #
    @5
    @10
    @6
    vw
    wex
    @8
    vz
    wex
    vx
    vw
    bj-el
    @8
    vx
    wal
    @8
    vz
    vz
    vx
    ax-nul
    @8
    vx
    sp
    eximii
    @6
    @8
    vw
    vz
    eeanv
    mpbir2an
    @9
    @4
    vw
    vz
    @6
    @3
    @7
    @3
    @6
    @7
    vw
    vz
    vx
    ax9
    com12
    con3dimp
    2eximi
    ax-mp
    @4
    @2
    vw
    vz
    vz
    vy
    weq
    #
    @4
    @2
    wi
    @11
    @4
    vw
    vy
    weq
    #
    wn
    #
    @2
    @11
    @3
    @12
    vz
    vy
    vw
    equequ2
    notbid
    @13
    @1
    vx
    vw
    vx
    vw
    weq
    @0
    @12
    vx
    vw
    vy
    ax7
    con3d
    bj-spimevv
    syl6bi
    @11
    wn
    #
    @2
    @4
    @14
    @1
    vx
    vz
    vx
    vz
    weq
    @0
    @11
    vx
    vz
    vy
    ax7
    con3d
    bj-spimevv
    a1d
    pm2.61i
    exlimivv
    ax-mp
    @0
    vx
    exnal
    mpbi
end
