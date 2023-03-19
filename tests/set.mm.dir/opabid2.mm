include "wrel.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "copab.mm"
include "wceq.mm"
include "wb.mm"
include "wal.mm"
include "vex.mm"
include "opeq1.mm"
include "eleq1d.mm"
include "opeq2.mm"
include "opelopab.mm"
include "gen2.mm"
include "relopab.mm"
include "eqrel.mm"
include "mpan.mm"
include "mpbiri.mm"

theorem opabid2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vw: setvar w
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cD: class D
  let wph: wff ph
  let wps: wff ps

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint ph z
  disjoint ph w
  disjoint ps z
  disjoint ps w
  assert |- ( Rel A -> { <. x , y >. | <. x , y >. e. A } = A )

  proof
    cA
    wrel
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cA
    wcel
    #
    vx
    vy
    copab
    #
    cA
    wceq
    #
    vz
    cv
    #
    vw
    cv
    #
    cop
    #
    @5
    wcel
    @9
    cA
    wcel
    #
    wb
    #
    vw
    wal
    vz
    wal
    #
    @11
    vz
    vw
    @4
    @7
    @2
    cop
    #
    cA
    wcel
    @10
    vx
    vy
    @7
    @8
    vz
    vex
    vw
    vex
    @1
    @7
    wceq
    @3
    @13
    cA
    @1
    @7
    @2
    opeq1
    eleq1d
    @2
    @8
    wceq
    @13
    @9
    cA
    @2
    @8
    @7
    opeq2
    eleq1d
    opelopab
    gen2
    @5
    wrel
    @0
    @6
    @12
    wb
    @4
    vx
    vy
    relopab
    vz
    vw
    @5
    cA
    eqrel
    mpan
    mpbiri
end
