include "wmo.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "nfmo1.mm"
include "nfa1.mm"
include "nfe1.mm"
include "nfmo.mm"
include "nfim.mm"
include "mopick.mm"
include "ex.mm"
include "com23.mm"
include "alrimd.mm"
include "moim.mm"
include "spsd.mm"
include "syl6.mm"
include "exlimd.mm"
include "wn.mm"
include "nfex.mm"
include "exsimpl.mm"
include "exlimi.mm"
include "exmo.mm"
include "ori.mm"
include "nsyl4.mm"
include "con1i.mm"
include "a1d.mm"
include "pm2.61d1.mm"
include "imp.mm"

theorem moexex
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume moexex.1: |- F/ y ph


  assert |- ( ( E* x ph /\ A. x E* y ps ) -> E* y E. x ( ph /\ ps ) )

  proof
    wph
    vx
    wmo
    #
    wps
    vy
    wmo
    #
    vx
    wal
    #
    wph
    wps
    wa
    #
    vx
    wex
    #
    vy
    wmo
    #
    @0
    wph
    vx
    wex
    #
    @2
    @5
    wi
    #
    @0
    wph
    @7
    vx
    wph
    vx
    nfmo1
    @2
    @5
    vx
    @1
    vx
    nfa1
    @4
    vx
    vy
    @3
    vx
    nfe1
    nfmo
    nfim
    @0
    wph
    @4
    wps
    wi
    #
    vy
    wal
    #
    @7
    @0
    wph
    @8
    vy
    wph
    vy
    vx
    moexex.1
    nfmo
    moexex.1
    @0
    @4
    wph
    wps
    @0
    @4
    wph
    wps
    wi
    wph
    wps
    vx
    mopick
    ex
    com23
    alrimd
    @9
    @1
    @5
    vx
    @4
    wps
    vy
    moim
    spsd
    syl6
    exlimd
    @6
    wn
    @5
    @2
    @5
    @6
    @4
    vy
    wex
    #
    @6
    @5
    @4
    @6
    vy
    wph
    vy
    vx
    moexex.1
    nfex
    wph
    wps
    vx
    exsimpl
    exlimi
    @10
    @5
    @4
    vy
    exmo
    ori
    nsyl4
    con1i
    a1d
    pm2.61d1
    imp
end
