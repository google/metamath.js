include "wmo.mm"
include "wn.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "cv.mm"
include "wne.mm"
include "wa.mm"
include "mo2.mm"
include "notbii.mm"
include "alnex.mm"
include "exnal.mm"
include "pm4.61.mm"
include "biid.mm"
include "necon3bbii.mm"
include "anbi2i.mm"
include "bitri.mm"
include "exbii.mm"
include "bitr3i.mm"
include "albii.mm"
include "3bitr2i.mm"

theorem nmo
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume nmo.1: |- F/ y ph

  disjoint x y
  assert |- ( -. E* x ph <-> A. y E. x ( ph /\ x =/= y ) )

  proof
    wph
    vx
    wmo
    #
    wn
    wph
    vx
    vy
    weq
    #
    wi
    #
    vx
    wal
    #
    vy
    wex
    #
    wn
    @3
    wn
    #
    vy
    wal
    wph
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    wa
    #
    vx
    wex
    #
    vy
    wal
    @0
    @4
    wph
    vx
    vy
    nmo.1
    mo2
    notbii
    @3
    vy
    alnex
    @5
    @10
    vy
    @5
    @2
    wn
    #
    vx
    wex
    @10
    @2
    vx
    exnal
    @11
    @9
    vx
    @11
    wph
    @1
    wn
    #
    wa
    @9
    wph
    @1
    pm4.61
    @12
    @8
    wph
    @1
    @6
    @7
    @1
    biid
    necon3bbii
    anbi2i
    bitri
    exbii
    bitr3i
    albii
    3bitr2i
end
