include "wn.mm"
include "weq.mm"
include "wsb.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "cv.mm"
include "wne.mm"
include "sbelx.mm"
include "sb56.mm"
include "sbn.mm"
include "imbi2i.mm"
include "con2b.mm"
include "df-ne.mm"
include "bicomi.mm"
include "3bitri.mm"
include "albii.mm"

theorem pm13.196a
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  disjoint ph y
  assert |- ( -. ph <-> A. y ( [ y / x ] ph -> y =/= x ) )

  proof
    wph
    wn
    #
    vy
    vx
    weq
    #
    @0
    vx
    vy
    wsb
    #
    wa
    vy
    wex
    @1
    @2
    wi
    #
    vy
    wal
    wph
    vx
    vy
    wsb
    #
    vy
    cv
    #
    vx
    cv
    #
    wne
    #
    wi
    #
    vy
    wal
    @0
    vy
    vx
    sbelx
    @2
    vy
    vx
    sb56
    @3
    @8
    vy
    @3
    @1
    @4
    wn
    #
    wi
    @4
    @1
    wn
    #
    wi
    @8
    @2
    @9
    @1
    wph
    vx
    vy
    sbn
    imbi2i
    @1
    @4
    con2b
    @10
    @7
    @4
    @7
    @10
    @5
    @6
    df-ne
    bicomi
    imbi2i
    3bitri
    albii
    3bitri
end
