include "wsb.mm"
include "wal.mm"
include "weq.mm"
include "wn.mm"
include "wa.mm"
include "ax-wl-11v.mm"
include "impbii.mm"
include "wb.mm"
include "nfna1.mm"
include "wl-ax11-lem3.mm"
include "nfan1.mm"
include "wl-ax11-lem5.mm"
include "adantl.mm"
include "albid.mm"
include "ancoms.mm"
include "syl5bb.mm"

theorem wl-ax11-lem6
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u

  disjoint u x
  assert |- ( ( A. u u = y /\ -. A. x x = y ) -> ( A. u A. x [ u / y ] ph <-> A. x A. y ph ) )

  proof
    wph
    vy
    vu
    wsb
    #
    vx
    wal
    vu
    wal
    #
    @0
    vu
    wal
    #
    vx
    wal
    #
    vu
    vy
    weq
    vu
    wal
    #
    vx
    vy
    weq
    #
    vx
    wal
    wn
    #
    wa
    wph
    vy
    wal
    #
    vx
    wal
    #
    @1
    @3
    @0
    vu
    vx
    ax-wl-11v
    @0
    vx
    vu
    ax-wl-11v
    impbii
    @6
    @4
    @3
    @8
    wb
    @6
    @4
    wa
    @2
    @7
    vx
    @6
    @4
    vx
    @5
    vx
    nfna1
    vx
    vy
    vu
    wl-ax11-lem3
    nfan1
    @4
    @2
    @7
    wb
    @6
    wph
    vy
    vu
    wl-ax11-lem5
    adantl
    albid
    ancoms
    syl5bb
end
