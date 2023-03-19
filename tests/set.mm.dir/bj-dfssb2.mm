include "wssb.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "df-ssb.mm"
include "bj-sb56.mm"
include "bicomi.mm"
include "anbi2i.mm"
include "exbii.mm"
include "3bitr2i.mm"

theorem bj-dfssb2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t

  disjoint t y
  disjoint x y
  disjoint ph y
  assert |- ( [b t /b x ]b ph <-> E. y ( y = t /\ E. x ( x = y /\ ph ) ) )

  proof
    wph
    vx
    vt
    wssb
    vy
    vt
    weq
    #
    vx
    vy
    weq
    #
    wph
    wi
    vx
    wal
    #
    wi
    vy
    wal
    @0
    @2
    wa
    #
    vy
    wex
    @0
    @1
    wph
    wa
    vx
    wex
    #
    wa
    #
    vy
    wex
    wph
    vx
    vy
    vt
    df-ssb
    @2
    vy
    vt
    bj-sb56
    @3
    @5
    vy
    @2
    @4
    @0
    @4
    @2
    wph
    vx
    vy
    bj-sb56
    bicomi
    anbi2i
    exbii
    3bitr2i
end
