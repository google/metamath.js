include "wnf.mm"
include "wal.mm"
include "wmo.mm"
include "wsb.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "nfa1.mm"
include "nfmo1.mm"
include "nfnf1.mm"
include "nfal.mm"
include "sp.mm"
include "nfmod.mm"
include "nfan1.mm"
include "wex.mm"
include "mo2v.mm"
include "spsbim.mm"
include "equsb3.mm"
include "syl6ib.mm"
include "anim12d.mm"
include "equtr2.mm"
include "syl6.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "adantl.mm"
include "alrimi.mm"
include "ex.mm"
include "alrimd.mm"
include "nfs1v.mm"
include "pm3.3.mm"
include "com23.mm"
include "sps.mm"
include "aleximi.mm"
include "alcoms.mm"
include "moabs.mm"
include "wl-sb8et.mm"
include "wl-mo2t.mm"
include "imbi12d.mm"
include "syl5bb.mm"
include "syl5ibr.mm"
include "impbid.mm"

theorem wl-mo3t
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u

  disjoint x y
  disjoint u x
  disjoint u y
  disjoint ph u
  assert |- ( A. x F/ y ph -> ( E* x ph <-> A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) )

  proof
    wph
    vy
    wnf
    #
    vx
    wal
    #
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
    #
    @1
    @2
    @7
    vx
    @0
    vx
    nfa1
    #
    wph
    vx
    nfmo1
    @1
    @2
    @7
    @1
    @2
    wa
    @6
    vy
    @1
    @2
    vy
    @0
    vy
    vx
    wph
    vy
    nfnf1
    nfal
    @1
    wph
    vy
    vx
    @9
    @0
    vx
    sp
    nfmod
    nfan1
    @2
    @6
    @1
    @2
    wph
    vx
    vu
    weq
    #
    wi
    #
    vx
    wal
    #
    vu
    wex
    @6
    wph
    vx
    vu
    mo2v
    @12
    @6
    vu
    @12
    @4
    @10
    vy
    vu
    weq
    #
    wa
    @5
    @12
    wph
    @10
    @3
    @13
    @11
    vx
    sp
    @12
    @3
    @10
    vx
    vy
    wsb
    @13
    wph
    @10
    vx
    vy
    spsbim
    vy
    vx
    vu
    equsb3
    syl6ib
    anim12d
    vx
    vy
    vu
    equtr2
    syl6
    exlimiv
    sylbi
    adantl
    alrimi
    ex
    alrimd
    @8
    @2
    @1
    @3
    vy
    wex
    #
    wph
    @5
    wi
    #
    vx
    wal
    #
    vy
    wex
    #
    wi
    #
    @6
    @18
    vy
    vx
    @6
    vx
    wal
    #
    @3
    @16
    vy
    @19
    @3
    @15
    vx
    @6
    vx
    nfa1
    wph
    vx
    vy
    nfs1v
    @6
    @3
    @15
    wi
    vx
    @6
    wph
    @3
    @5
    wph
    @3
    @5
    pm3.3
    com23
    sps
    alrimd
    aleximi
    alcoms
    @2
    wph
    vx
    wex
    #
    @2
    wi
    @1
    @18
    wph
    vx
    moabs
    @1
    @20
    @14
    @2
    @17
    wph
    vx
    vy
    wl-sb8et
    wph
    vx
    vy
    wl-mo2t
    imbi12d
    syl5bb
    syl5ibr
    impbid
end
