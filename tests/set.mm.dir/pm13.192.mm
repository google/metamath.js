include "cv.mm"
include "wceq.mm"
include "weq.mm"
include "wb.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "wsbc.mm"
include "wi.mm"
include "biimpr.mm"
include "alimi.mm"
include "eqeq1.mm"
include "equsalvw.mm"
include "sylib.mm"
include "eqeq2.mm"
include "eqcoms.mm"
include "alrimiv.mm"
include "impbii.mm"
include "anbi1i.mm"
include "exbii.mm"
include "sbc5.mm"
include "bitr4i.mm"

theorem pm13.192
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( E. y ( A. x ( x = A <-> x = y ) /\ ph ) <-> [. A / y ]. ph )

  proof
    vx
    cv
    #
    cA
    wceq
    #
    vx
    vy
    weq
    #
    wb
    #
    vx
    wal
    #
    wph
    wa
    #
    vy
    wex
    vy
    cv
    #
    cA
    wceq
    #
    wph
    wa
    #
    vy
    wex
    wph
    vy
    cA
    wsbc
    @5
    @8
    vy
    @4
    @7
    wph
    @4
    @7
    @4
    @2
    @1
    wi
    #
    vx
    wal
    @7
    @3
    @9
    vx
    @1
    @2
    biimpr
    alimi
    @1
    @7
    vx
    vy
    @0
    @6
    cA
    eqeq1
    equsalvw
    sylib
    @7
    @3
    vx
    @3
    cA
    @6
    cA
    @6
    @0
    eqeq2
    eqcoms
    alrimiv
    impbii
    anbi1i
    exbii
    wph
    vy
    cA
    sbc5
    bitr4i
end
