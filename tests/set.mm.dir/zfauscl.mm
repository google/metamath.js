include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "wceq.mm"
include "eleq2.mm"
include "anbi1d.mm"
include "bibi2d.mm"
include "albidv.mm"
include "exbidv.mm"
include "ax-sep.mm"
include "vtocl.mm"

theorem zfauscl
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume zfauscl.1: |- A e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint ph y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint ph z
  assert |- E. y A. x ( x e. y <-> ( x e. A /\ ph ) )

  proof
    vx
    cv
    #
    vy
    cv
    wcel
    #
    @0
    vz
    cv
    #
    wcel
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
    @0
    cA
    wcel
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
    vz
    cA
    zfauscl.1
    @2
    cA
    wceq
    #
    @6
    @10
    vy
    @11
    @5
    @9
    vx
    @11
    @4
    @8
    @1
    @11
    @3
    @7
    wph
    @2
    cA
    @0
    eleq2
    anbi1d
    bibi2d
    albidv
    exbidv
    wph
    vx
    vy
    vz
    ax-sep
    vtocl
end
