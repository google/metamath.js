include "weq.mm"
include "wa.mm"
include "wex.mm"
include "wsb.mm"
include "19.41.mm"
include "exbii.mm"
include "bitri.mm"
include "sbequ12r.mm"
include "sylan9bb.mm"
include "pm5.32i.mm"
include "2exbii.mm"
include "2ax6e.mm"
include "biantrur.mm"
include "3bitr4ri.mm"

theorem 2sb5rf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume 2sb5rf.1: |- F/ z ph
  assume 2sb5rf.2: |- F/ w ph

  disjoint w z
  assert |- ( ph <-> E. z E. w ( ( z = x /\ w = y ) /\ [ z / x ] [ w / y ] ph ) )

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
    wa
    #
    vw
    wex
    #
    vz
    wex
    #
    @2
    vw
    wex
    #
    vz
    wex
    #
    wph
    wa
    #
    @2
    wph
    vy
    vw
    wsb
    #
    vx
    vz
    wsb
    #
    wa
    #
    vw
    wex
    vz
    wex
    wph
    @5
    @6
    wph
    wa
    #
    vz
    wex
    @8
    @4
    @12
    vz
    @2
    wph
    vw
    2sb5rf.2
    19.41
    exbii
    @6
    wph
    vz
    2sb5rf.1
    19.41
    bitri
    @11
    @3
    vz
    vw
    @2
    @10
    wph
    @0
    @10
    @9
    @1
    wph
    @9
    vz
    vx
    sbequ12r
    wph
    vw
    vy
    sbequ12r
    sylan9bb
    pm5.32i
    2exbii
    @7
    wph
    vx
    vy
    vz
    vw
    2ax6e
    biantrur
    3bitr4ri
end
