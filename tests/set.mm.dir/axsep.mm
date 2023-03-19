include "wel.mm"
include "weq.mm"
include "wa.mm"
include "wex.mm"
include "wb.mm"
include "wal.mm"
include "wi.mm"
include "nfv.mm"
include "axrep5.mm"
include "equtr.mm"
include "equcomi.mm"
include "syl6.mm"
include "adantrd.mm"
include "alrimiv.mm"
include "a1d.mm"
include "spimev.mm"
include "mpg.mm"
include "an12.mm"
include "exbii.mm"
include "elequ1.mm"
include "anbi1d.mm"
include "equsexvw.mm"
include "bitr3i.mm"
include "bibi2i.mm"
include "albii.mm"
include "mpbi.mm"

theorem axsep
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ph w
  assert |- E. y A. x ( x e. y <-> ( x e. z /\ ph ) )

  proof
    vx
    vy
    wel
    #
    vw
    vz
    wel
    #
    vw
    vx
    weq
    #
    wph
    wa
    #
    wa
    #
    vw
    wex
    #
    wb
    #
    vx
    wal
    #
    vy
    wex
    #
    @0
    vx
    vz
    wel
    #
    wph
    wa
    #
    wb
    #
    vx
    wal
    #
    vy
    wex
    @1
    @3
    vx
    vy
    weq
    #
    wi
    #
    vx
    wal
    #
    vy
    wex
    wi
    @8
    vw
    @3
    vw
    vx
    vy
    vz
    @3
    vy
    nfv
    axrep5
    @1
    @15
    vy
    vw
    vy
    vw
    weq
    #
    @15
    @1
    @16
    @14
    vx
    @16
    @2
    @13
    wph
    @16
    @2
    vy
    vx
    weq
    @13
    vy
    vw
    vx
    equtr
    vy
    vx
    equcomi
    syl6
    adantrd
    alrimiv
    a1d
    spimev
    mpg
    @7
    @12
    vy
    @6
    @11
    vx
    @5
    @10
    @0
    @5
    @2
    @1
    wph
    wa
    #
    wa
    #
    vw
    wex
    @10
    @18
    @4
    vw
    @2
    @1
    wph
    an12
    exbii
    @17
    @10
    vw
    vx
    @2
    @1
    @9
    wph
    vw
    vx
    vz
    elequ1
    anbi1d
    equsexvw
    bitr3i
    bibi2i
    albii
    exbii
    mpbi
end
