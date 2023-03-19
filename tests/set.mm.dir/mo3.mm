include "wmo.mm"
include "wsb.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "nfmo1.mm"
include "nfmo.mm"
include "wex.mm"
include "mo2v.mm"
include "sp.mm"
include "spsbim.mm"
include "equsb3.mm"
include "syl6ib.mm"
include "anim12d.mm"
include "equtr2.mm"
include "syl6.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "alrimi.mm"
include "nfs1v.mm"
include "pm3.21.mm"
include "imim1d.mm"
include "alimd.mm"
include "com12.mm"
include "aleximi.mm"
include "sb8e.mm"
include "mo2.mm"
include "3imtr4g.mm"
include "moabs.mm"
include "sylibr.mm"
include "alcoms.mm"
include "impbii.mm"

theorem mo3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume mo3.1: |- F/ y ph

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ph z
  assert |- ( E* x ph <-> A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) )

  proof
    wph
    vx
    wmo
    #
    wph
    wph
    vx
    vy
    wsb
    #
    wa
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    wal
    #
    vx
    wal
    @0
    @5
    vx
    wph
    vx
    nfmo1
    @0
    @4
    vy
    wph
    vy
    vx
    mo3.1
    nfmo
    @0
    wph
    vx
    vz
    weq
    #
    wi
    #
    vx
    wal
    #
    vz
    wex
    @4
    wph
    vx
    vz
    mo2v
    @8
    @4
    vz
    @8
    @2
    @6
    vy
    vz
    weq
    #
    wa
    @3
    @8
    wph
    @6
    @1
    @9
    @7
    vx
    sp
    @8
    @1
    @6
    vx
    vy
    wsb
    @9
    wph
    @6
    vx
    vy
    spsbim
    vy
    vx
    vz
    equsb3
    syl6ib
    anim12d
    vx
    vy
    vz
    equtr2
    syl6
    exlimiv
    sylbi
    alrimi
    alrimi
    @4
    @0
    vy
    vx
    @4
    vx
    wal
    #
    vy
    wal
    #
    wph
    vx
    wex
    #
    @0
    wi
    @0
    @11
    @1
    vy
    wex
    wph
    @3
    wi
    #
    vx
    wal
    #
    vy
    wex
    @12
    @0
    @10
    @1
    @14
    vy
    @1
    @10
    @14
    @1
    @4
    @13
    vx
    wph
    vx
    vy
    nfs1v
    @1
    wph
    @2
    @3
    @1
    wph
    pm3.21
    imim1d
    alimd
    com12
    aleximi
    wph
    vx
    vy
    mo3.1
    sb8e
    wph
    vx
    vy
    mo3.1
    mo2
    3imtr4g
    wph
    vx
    moabs
    sylibr
    alcoms
    impbii
end
