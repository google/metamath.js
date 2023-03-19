include "weq.mm"
include "wal.mm"
include "wn.mm"
include "nfna1.mm"
include "wl-naev.mm"
include "wa.mm"
include "nfa1.mm"
include "nfan.mm"
include "wi.mm"
include "axc11n.mm"
include "wl-aetr.mm"
include "syl5.mm"
include "aecoms.mm"
include "con3d.mm"
include "imdistani.mm"
include "wl-ax11-lem2.mm"
include "syl.mm"
include "alrimi.mm"
include "sylan2.mm"
include "expcom.mm"
include "ax-wl-11v.mm"
include "syl6.mm"
include "nf5d.mm"

theorem wl-ax11-lem3
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u

  disjoint u x
  assert |- ( -. A. x x = y -> F/ x A. u u = y )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    #
    wn
    #
    vu
    vy
    weq
    #
    vu
    wal
    #
    vx
    @0
    vx
    nfna1
    @2
    @4
    @3
    vx
    wal
    #
    vu
    wal
    #
    @4
    vx
    wal
    @4
    @2
    @6
    @2
    @4
    vu
    vx
    weq
    #
    vu
    wal
    #
    wn
    #
    @6
    vx
    vy
    vx
    vu
    wl-naev
    @4
    @9
    wa
    #
    @5
    vu
    @4
    @9
    vu
    @3
    vu
    nfa1
    @7
    vu
    nfna1
    nfan
    @10
    @4
    @2
    wa
    @5
    @4
    @9
    @2
    @4
    @1
    @8
    @1
    @8
    wi
    vy
    vu
    @1
    vy
    vx
    weq
    vy
    wal
    vy
    vu
    weq
    vy
    wal
    @8
    vx
    vy
    axc11n
    vy
    vu
    vx
    wl-aetr
    syl5
    aecoms
    con3d
    imdistani
    vx
    vy
    vu
    wl-ax11-lem2
    syl
    alrimi
    sylan2
    expcom
    @3
    vu
    vx
    ax-wl-11v
    syl6
    nf5d
end
