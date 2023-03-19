include "wel.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wa.mm"
include "wb.mm"
include "19.37v.mm"
include "impexp.mm"
include "albii.mm"
include "19.21v.mm"
include "bitr2i.mm"
include "exbii.mm"
include "bitr3i.mm"
include "nfv.mm"
include "nfan.mm"
include "bj-axrep4.mm"
include "sylbi.mm"
include "anabs5.mm"
include "bibi2i.mm"
include "sylib.mm"

theorem bj-axrep5
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume bj-axrep5.1: |- F/ z ph

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  assert |- ( A. x ( x e. w -> E. z A. y ( ph -> y = z ) ) -> E. z A. y ( y e. z <-> E. x ( x e. w /\ ph ) ) )

  proof
    vx
    vw
    wel
    #
    wph
    vy
    vz
    weq
    #
    wi
    #
    vy
    wal
    #
    vz
    wex
    wi
    #
    vx
    wal
    #
    vy
    vz
    wel
    #
    @0
    @0
    wph
    wa
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
    vz
    wex
    #
    @6
    @7
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
    @5
    @7
    @1
    wi
    #
    vy
    wal
    #
    vz
    wex
    #
    vx
    wal
    @12
    @4
    @18
    vx
    @4
    @0
    @3
    wi
    #
    vz
    wex
    @18
    @0
    @3
    vz
    19.37v
    @19
    @17
    vz
    @17
    @0
    @2
    wi
    #
    vy
    wal
    @19
    @16
    @20
    vy
    @0
    wph
    @1
    impexp
    albii
    @0
    @2
    vy
    19.21v
    bitr2i
    exbii
    bitr3i
    albii
    @7
    vx
    vy
    vz
    vw
    @0
    wph
    vz
    @0
    vz
    nfv
    bj-axrep5.1
    nfan
    bj-axrep4
    sylbi
    @11
    @15
    vz
    @10
    @14
    vy
    @9
    @13
    @6
    @8
    @7
    vx
    @0
    wph
    anabs5
    exbii
    bibi2i
    albii
    exbii
    sylib
end
