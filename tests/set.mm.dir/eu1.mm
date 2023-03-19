include "wsb.mm"
include "weu.mm"
include "weq.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "wi.mm"
include "wa.mm"
include "nfs1v.mm"
include "euf.mm"
include "sb8eu.mm"
include "sb6rf.mm"
include "equcom.mm"
include "imbi2i.mm"
include "albii.mm"
include "anbi12ci.mm"
include "albiim.mm"
include "bitr4i.mm"
include "exbii.mm"
include "3bitr4i.mm"

theorem eu1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume eu1.1: |- F/ y ph

  disjoint x y
  assert |- ( E! x ph <-> E. x ( ph /\ A. y ( [ y / x ] ph -> x = y ) ) )

  proof
    wph
    vx
    vy
    wsb
    #
    vy
    weu
    @0
    vy
    vx
    weq
    #
    wb
    vy
    wal
    #
    vx
    wex
    wph
    vx
    weu
    wph
    @0
    vx
    vy
    weq
    #
    wi
    #
    vy
    wal
    #
    wa
    #
    vx
    wex
    @0
    vy
    vx
    wph
    vx
    vy
    nfs1v
    euf
    wph
    vx
    vy
    eu1.1
    sb8eu
    @6
    @2
    vx
    @6
    @0
    @1
    wi
    #
    vy
    wal
    #
    @1
    @0
    wi
    vy
    wal
    #
    wa
    @2
    wph
    @9
    @5
    @8
    wph
    vx
    vy
    eu1.1
    sb6rf
    @4
    @7
    vy
    @3
    @1
    @0
    vx
    vy
    equcom
    imbi2i
    albii
    anbi12ci
    @0
    @1
    vy
    albiim
    bitr4i
    exbii
    3bitr4i
end
