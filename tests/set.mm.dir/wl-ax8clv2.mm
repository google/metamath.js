include "weq.mm"
include "wa.mm"
include "wex.mm"
include "wcel2-wl.mm"
include "wi.mm"
include "equvinv.mm"
include "wcel-wl.mm"
include "wal.mm"
include "df-wl-clelv2.mm"
include "equtrr.mm"
include "imim1d.mm"
include "alimdv.mm"
include "syl5bi.mm"
include "equeuclr.mm"
include "syl6ibr.mm"
include "sylan9.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem wl-ax8clv2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vt: setvar t
  let vu: setvar u


  assert |- ( x = y -> ( x wl-el2 A -> y wl-el2 A ) )

  proof
    vx
    vy
    weq
    vu
    vx
    weq
    #
    vu
    vy
    weq
    #
    wa
    #
    vu
    wex
    vx
    cA
    wcel2-wl
    #
    vy
    cA
    wcel2-wl
    #
    wi
    #
    vx
    vy
    vu
    equvinv
    @2
    @5
    vu
    @0
    @3
    vt
    vu
    weq
    #
    vt
    cA
    wcel-wl
    #
    wi
    #
    vt
    wal
    #
    @1
    @4
    @3
    vt
    vx
    weq
    #
    @7
    wi
    #
    vt
    wal
    @0
    @9
    vx
    vt
    cA
    df-wl-clelv2
    @0
    @11
    @8
    vt
    @0
    @6
    @10
    @7
    vu
    vx
    vt
    equtrr
    imim1d
    alimdv
    syl5bi
    @1
    @9
    vt
    vy
    weq
    #
    @7
    wi
    #
    vt
    wal
    @4
    @1
    @8
    @13
    vt
    @1
    @12
    @6
    @7
    vu
    vt
    vy
    equeuclr
    imim1d
    alimdv
    vy
    vt
    cA
    df-wl-clelv2
    syl6ibr
    sylan9
    exlimiv
    sylbi
end
