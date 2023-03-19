include "wex.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wb.mm"
include "copab.mm"
include "cdm.mm"
include "wceq.mm"
include "df-ral.mm"
include "pm4.71.mm"
include "albii.mm"
include "cab.mm"
include "dmopab.mm"
include "19.42v.mm"
include "abbii.mm"
include "eqtri.mm"
include "eqeq1i.mm"
include "eqcom.mm"
include "abeq2.mm"
include "3bitr2ri.mm"
include "3bitri.mm"

theorem dmopab3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( A. x e. A E. y ph <-> dom { <. x , y >. | ( x e. A /\ ph ) } = A )

  proof
    wph
    vy
    wex
    #
    vx
    cA
    wral
    vx
    cv
    cA
    wcel
    #
    @0
    wi
    #
    vx
    wal
    @1
    @1
    @0
    wa
    #
    wb
    #
    vx
    wal
    #
    @1
    wph
    wa
    #
    vx
    vy
    copab
    cdm
    #
    cA
    wceq
    #
    @0
    vx
    cA
    df-ral
    @2
    @4
    vx
    @1
    @0
    pm4.71
    albii
    @8
    @3
    vx
    cab
    #
    cA
    wceq
    cA
    @9
    wceq
    @5
    @7
    @9
    cA
    @7
    @6
    vy
    wex
    #
    vx
    cab
    @9
    @6
    vx
    vy
    dmopab
    @10
    @3
    vx
    @1
    wph
    vy
    19.42v
    abbii
    eqtri
    eqeq1i
    cA
    @9
    eqcom
    @3
    vx
    cA
    abeq2
    3bitr2ri
    3bitri
end
