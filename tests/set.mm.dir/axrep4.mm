include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wel.mm"
include "wa.mm"
include "wb.mm"
include "axrep3.mm"
include "19.35i.mm"
include "nfv.mm"
include "nfa1.mm"
include "nfan.mm"
include "nfex.mm"
include "nfbi.mm"
include "nfal.mm"
include "nfe1.mm"
include "elequ2.mm"
include "19.3.mm"
include "anbi2i.mm"
include "exbii.mm"
include "a1i.mm"
include "bibi12d.mm"
include "albidv.mm"
include "cbvex.mm"
include "sylib.mm"

theorem axrep4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume axrep4.1: |- F/ z ph

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  assert |- ( A. x E. z A. y ( ph -> y = z ) -> E. z A. y ( y e. z <-> E. x ( x e. w /\ ph ) ) )

  proof
    wph
    vy
    vz
    weq
    wi
    vy
    wal
    vz
    wex
    #
    vx
    wal
    vy
    vx
    wel
    #
    vx
    vw
    wel
    #
    wph
    vz
    wal
    #
    wa
    #
    vx
    wex
    #
    wb
    #
    vy
    wal
    #
    vx
    wex
    vy
    vz
    wel
    #
    @2
    wph
    wa
    #
    vx
    wex
    #
    wb
    #
    vy
    wal
    #
    vz
    wex
    @0
    @7
    vx
    wph
    vx
    vz
    vy
    vw
    axrep3
    19.35i
    @7
    @12
    vx
    vz
    @6
    vz
    vy
    @1
    @5
    vz
    @1
    vz
    nfv
    @4
    vz
    vx
    @2
    @3
    vz
    @2
    vz
    nfv
    wph
    vz
    nfa1
    nfan
    nfex
    nfbi
    nfal
    @11
    vx
    vy
    @8
    @10
    vx
    @8
    vx
    nfv
    @9
    vx
    nfe1
    nfbi
    nfal
    vx
    vz
    weq
    #
    @6
    @11
    vy
    @13
    @1
    @8
    @5
    @10
    vx
    vz
    vy
    elequ2
    @5
    @10
    wb
    @13
    @4
    @9
    vx
    @3
    wph
    @2
    wph
    vz
    axrep4.1
    19.3
    anbi2i
    exbii
    a1i
    bibi12d
    albidv
    cbvex
    sylib
end
