include "wal.mm"
include "weq.mm"
include "wi.mm"
include "wex.mm"
include "wel.mm"
include "wa.mm"
include "wb.mm"
include "nfe1.mm"
include "nfv.mm"
include "nfim.mm"
include "nfex.mm"
include "elequ2.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "bibi2d.mm"
include "albidv.mm"
include "imbi2d.mm"
include "axrep1.mm"
include "chvar.mm"
include "sp.mm"
include "imim1i.mm"
include "alimi.mm"
include "eximi.mm"
include "nfa1.mm"
include "nfal.mm"
include "equequ2.mm"
include "cbvex.mm"
include "sylib.mm"
include "eximii.mm"

theorem axrep2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ph w
  disjoint w x
  disjoint w y
  disjoint w z
  assert |- E. x ( E. y A. z ( ph -> z = y ) -> A. z ( z e. x <-> E. x ( x e. y /\ A. y ph ) ) )

  proof
    wph
    vy
    wal
    #
    vz
    vw
    weq
    #
    wi
    #
    vz
    wal
    #
    vw
    wex
    #
    vz
    vx
    wel
    #
    vx
    vy
    wel
    #
    @0
    wa
    #
    vx
    wex
    #
    wb
    #
    vz
    wal
    #
    wi
    #
    wph
    vz
    vy
    weq
    #
    wi
    #
    vz
    wal
    #
    vy
    wex
    #
    @10
    wi
    vx
    @4
    @5
    vx
    vw
    wel
    #
    @0
    wa
    #
    vx
    wex
    #
    wb
    #
    vz
    wal
    #
    wi
    #
    vx
    wex
    @11
    vx
    wex
    vw
    vy
    @11
    vw
    vx
    @4
    @10
    vw
    @3
    vw
    nfe1
    @10
    vw
    nfv
    nfim
    nfex
    vw
    vy
    weq
    #
    @21
    @11
    vx
    @22
    @20
    @10
    @4
    @22
    @19
    @9
    vz
    @22
    @18
    @8
    @5
    @22
    @17
    @7
    vx
    @22
    @16
    @6
    @0
    vw
    vy
    vx
    elequ2
    anbi1d
    exbidv
    bibi2d
    albidv
    imbi2d
    exbidv
    @0
    vx
    vw
    vz
    axrep1
    chvar
    @15
    @4
    @10
    @15
    @0
    @12
    wi
    #
    vz
    wal
    #
    vy
    wex
    @4
    @14
    @24
    vy
    @13
    @23
    vz
    @0
    wph
    @12
    wph
    vy
    sp
    imim1i
    alimi
    eximi
    @24
    @3
    vy
    vw
    @24
    vw
    nfv
    @2
    vy
    vz
    @0
    @1
    vy
    wph
    vy
    nfa1
    @1
    vy
    nfv
    nfim
    nfal
    vy
    vw
    weq
    #
    @23
    @2
    vz
    @25
    @12
    @1
    @0
    vy
    vw
    vz
    equequ2
    imbi2d
    albidv
    cbvex
    sylib
    imim1i
    eximii
end
