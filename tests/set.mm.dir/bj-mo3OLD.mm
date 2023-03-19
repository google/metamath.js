include "wmo.mm"
include "wsb.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "mo2v.mm"
include "nfv.mm"
include "nfim.mm"
include "nfs1v.mm"
include "sbequ2.mm"
include "ax7.mm"
include "imim12d.mm"
include "cbv3.mm"
include "ancli.mm"
include "aaan.mm"
include "sylibr.mm"
include "prth.mm"
include "equtr2.mm"
include "syl6.mm"
include "2alimi.mm"
include "syl.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "nfa1.mm"
include "pm3.3.mm"
include "com3r.mm"
include "alimd.mm"
include "com12.mm"
include "sps.mm"
include "eximd.mm"
include "sb8e.mm"
include "mo2.mm"
include "3imtr4g.mm"
include "moabs.mm"
include "alcoms.mm"
include "impbii.mm"

theorem bj-mo3OLD
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume bj-mo3OLD.nf: |- F/ y ph

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
    vx
    wal
    #
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
    @5
    wph
    vx
    vz
    mo2v
    @8
    @5
    vz
    @8
    @7
    @1
    vy
    vz
    weq
    #
    wi
    #
    wa
    #
    vy
    wal
    vx
    wal
    #
    @5
    @8
    @8
    @10
    vy
    wal
    #
    wa
    @12
    @8
    @13
    @7
    @10
    vx
    vy
    wph
    @6
    vy
    bj-mo3OLD.nf
    @6
    vy
    nfv
    nfim
    #
    @1
    @9
    vx
    wph
    vx
    vy
    nfs1v
    #
    @9
    vx
    nfv
    nfim
    #
    @3
    @1
    wph
    @6
    @9
    wph
    vx
    vy
    sbequ2
    vx
    vy
    vz
    ax7
    imim12d
    cbv3
    ancli
    @7
    @10
    vx
    vy
    @14
    @16
    aaan
    sylibr
    @11
    @4
    vx
    vy
    @11
    @2
    @6
    @9
    wa
    @3
    wph
    @6
    @1
    @9
    prth
    vx
    vy
    vz
    equtr2
    syl6
    2alimi
    syl
    exlimiv
    sylbi
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
    @18
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
    @19
    @0
    @18
    @1
    @21
    vy
    @17
    vy
    nfa1
    @17
    @1
    @21
    wi
    vy
    @1
    @17
    @21
    @1
    @4
    @20
    vx
    @15
    @4
    wph
    @1
    @3
    wph
    @1
    @3
    pm3.3
    com3r
    alimd
    com12
    sps
    eximd
    wph
    vx
    vy
    bj-mo3OLD.nf
    sb8e
    wph
    vx
    vy
    bj-mo3OLD.nf
    mo2
    3imtr4g
    wph
    vx
    moabs
    sylibr
    alcoms
    impbii
end
