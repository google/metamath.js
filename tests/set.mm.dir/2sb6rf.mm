include "weq.mm"
include "wa.mm"
include "wsb.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "sbequ12r.mm"
include "sylan9bb.mm"
include "pm5.74i.mm"
include "2albii.mm"
include "19.23.mm"
include "albii.mm"
include "bitri.mm"
include "wb.mm"
include "2ax6e.mm"
include "pm5.5.mm"
include "ax-mp.mm"
include "3bitrri.mm"

theorem 2sb6rf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume 2sb5rf.1: |- F/ z ph
  assume 2sb5rf.2: |- F/ w ph

  disjoint w z
  assert |- ( ph <-> A. z A. w ( ( z = x /\ w = y ) -> [ z / x ] [ w / y ] ph ) )

  proof
    vz
    vx
    weq
    #
    vw
    vy
    weq
    #
    wa
    #
    wph
    vy
    vw
    wsb
    #
    vx
    vz
    wsb
    #
    wi
    #
    vw
    wal
    vz
    wal
    @2
    wph
    wi
    #
    vw
    wal
    #
    vz
    wal
    #
    @2
    vw
    wex
    #
    vz
    wex
    #
    wph
    wi
    #
    wph
    @5
    @6
    vz
    vw
    @2
    @4
    wph
    @0
    @4
    @3
    @1
    wph
    @3
    vz
    vx
    sbequ12r
    wph
    vw
    vy
    sbequ12r
    sylan9bb
    pm5.74i
    2albii
    @8
    @9
    wph
    wi
    #
    vz
    wal
    @11
    @7
    @12
    vz
    @2
    wph
    vw
    2sb5rf.2
    19.23
    albii
    @9
    wph
    vz
    2sb5rf.1
    19.23
    bitri
    @10
    @11
    wph
    wb
    vx
    vy
    vz
    vw
    2ax6e
    @10
    wph
    pm5.5
    ax-mp
    3bitrri
end
