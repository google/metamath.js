include "weq.mm"
include "wn.mm"
include "wex.mm"
include "wal.mm"
include "wel.mm"
include "wa.mm"
include "el.mm"
include "ax-nul.mm"
include "sp.mm"
include "eximii.mm"
include "eeanv.mm"
include "mpbir2an.mm"
include "ax9.mm"
include "com12.mm"
include "con3dimp.mm"
include "2eximi.mm"
include "wi.mm"
include "equequ2.mm"
include "notbid.mm"
include "ax7.mm"
include "con3d.mm"
include "spimev.mm"
include "syl6bi.mm"
include "a1d.mm"
include "pm2.61i.mm"
include "exlimivv.mm"
include "mp2b.mm"
include "exnal.mm"
include "mpbi.mm"

theorem dtru
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
    @2
    @7
    @3
    vw
    wex
    @5
    vz
    wex
    vx
    vw
    el
    @5
    vx
    wal
    @5
    vz
    vz
    vx
    ax-nul
    @5
    vx
    sp
    eximii
    @3
    @5
    vw
    vz
    eeanv
    mpbir2an
    @6
    @9
    vw
    vz
    @3
    @8
    @4
    @8
    @3
    @4
    vw
    vz
    vx
    ax9
    com12
    con3dimp
    2eximi
    @9
    @2
    vw
    vz
    vz
    vy
    weq
    #
    @9
    @2
    wi
    @10
    @9
    vw
    vy
    weq
    #
    wn
    #
    @2
    @10
    @8
    @11
    vz
    vy
    vw
    equequ2
    notbid
    @12
    @1
    vx
    vw
    vx
    vw
    weq
    @0
    @11
    vx
    vw
    vy
    ax7
    con3d
    spimev
    syl6bi
    @10
    wn
    #
    @2
    @9
    @13
    @1
    vx
    vz
    vx
    vz
    weq
    @0
    @10
    vx
    vz
    vy
    ax7
    con3d
    spimev
    a1d
    pm2.61i
    exlimivv
    mp2b
    @0
    vx
    exnal
    mpbi
end
