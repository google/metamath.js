include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wsb.mm"
include "wb.mm"
include "axc11n.mm"
include "con3i.mm"
include "wa.mm"
include "wi.mm"
include "wl-ax11-lem1.mm"
include "notbid.mm"
include "anbi1d.mm"
include "wl-ax11-lem4.mm"
include "sbequ12.mm"
include "equcoms.mm"
include "sps.mm"
include "adantr.mm"
include "albid.mm"
include "ex.mm"
include "syl5.mm"
include "pm5.32d.mm"
include "bitr4d.mm"
include "dral1.mm"
include "wl-ax11-lem7.mm"
include "3bitr3g.mm"
include "bitr3d.mm"
include "pm5.32.mm"
include "sylibr.mm"
include "imp.mm"
include "sylan2.mm"

theorem wl-ax11-lem8
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u

  disjoint u x
  assert |- ( ( A. u u = y /\ -. A. x x = y ) -> ( A. u A. x [ u / y ] ph <-> A. y A. x ph ) )

  proof
    vx
    vy
    weq
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
    vy
    vx
    weq
    vy
    wal
    #
    wn
    #
    wph
    vy
    vu
    wsb
    #
    vx
    wal
    #
    vu
    wal
    #
    wph
    vx
    wal
    #
    vy
    wal
    #
    wb
    #
    @4
    @0
    vy
    vx
    axc11n
    con3i
    @3
    @5
    @11
    @3
    @5
    @8
    wa
    #
    @5
    @10
    wa
    #
    wb
    @5
    @11
    wi
    @3
    vu
    vx
    weq
    vu
    wal
    #
    wn
    #
    @8
    wa
    #
    @12
    @13
    @3
    @15
    @5
    @8
    @3
    @14
    @4
    vu
    vy
    vx
    wl-ax11-lem1
    notbid
    #
    anbi1d
    @3
    @15
    @7
    wa
    #
    vu
    wal
    @5
    @9
    wa
    #
    vy
    wal
    @16
    @13
    @18
    @19
    vu
    vy
    @3
    @18
    @5
    @7
    wa
    @19
    @3
    @15
    @5
    @7
    @17
    anbi1d
    @3
    @5
    @9
    @7
    @5
    @1
    @3
    @9
    @7
    wb
    #
    @0
    @4
    vx
    vy
    axc11n
    con3i
    @3
    @1
    @20
    @3
    @1
    wa
    wph
    @6
    vx
    vx
    vy
    vu
    wl-ax11-lem4
    @3
    wph
    @6
    wb
    #
    @1
    @2
    @21
    vu
    @21
    vy
    vu
    wph
    vy
    vu
    sbequ12
    equcoms
    sps
    adantr
    albid
    ex
    syl5
    pm5.32d
    bitr4d
    dral1
    @7
    vu
    vx
    wl-ax11-lem7
    @9
    vy
    vx
    wl-ax11-lem7
    3bitr3g
    bitr3d
    @5
    @8
    @10
    pm5.32
    sylibr
    imp
    sylan2
end
