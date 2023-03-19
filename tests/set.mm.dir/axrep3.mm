include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wel.mm"
include "wa.mm"
include "wb.mm"
include "nfe1.mm"
include "nfv.mm"
include "nfa1.mm"
include "nfan.mm"
include "nfex.mm"
include "nfbi.mm"
include "nfal.mm"
include "nfim.mm"
include "elequ2.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "bibi2d.mm"
include "albidv.mm"
include "imbi2d.mm"
include "axrep2.mm"
include "chvar.mm"

theorem axrep3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- E. x ( E. y A. z ( ph -> z = y ) -> A. z ( z e. x <-> E. x ( x e. w /\ A. y ph ) ) )

  proof
    wph
    vz
    vy
    weq
    wi
    vz
    wal
    #
    vy
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
    wph
    vy
    wal
    #
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
    @1
    @2
    vx
    vw
    wel
    #
    @4
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
    vy
    vw
    @15
    vy
    vx
    @1
    @14
    vy
    @0
    vy
    nfe1
    @13
    vy
    vz
    @2
    @12
    vy
    @2
    vy
    nfv
    @11
    vy
    vx
    @10
    @4
    vy
    @10
    vy
    nfv
    wph
    vy
    nfa1
    nfan
    nfex
    nfbi
    nfal
    nfim
    nfex
    vy
    vw
    weq
    #
    @9
    @15
    vx
    @16
    @8
    @14
    @1
    @16
    @7
    @13
    vz
    @16
    @6
    @12
    @2
    @16
    @5
    @11
    vx
    @16
    @3
    @10
    @4
    vy
    vw
    vx
    elequ2
    anbi1d
    exbidv
    bibi2d
    albidv
    imbi2d
    exbidv
    wph
    vx
    vy
    vz
    axrep2
    chvar
end
