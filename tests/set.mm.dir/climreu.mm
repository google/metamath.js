include "cli.mm"
include "wbr.mm"
include "cv.mm"
include "weu.mm"
include "cc.mm"
include "wreu.mm"
include "climeu.mm"
include "wcel.mm"
include "wa.mm"
include "climcl.mm"
include "pm4.71ri.mm"
include "eubii.mm"
include "df-reu.mm"
include "bitr4i.mm"
include "sylib.mm"

theorem climreu
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y

  disjoint F x
  disjoint A y
  disjoint x y
  disjoint F y
  assert |- ( F ~~> A -> E! x e. CC F ~~> x )

  proof
    cF
    cA
    cli
    wbr
    cF
    vx
    cv
    #
    cli
    wbr
    #
    vx
    weu
    #
    @1
    vx
    cc
    wreu
    #
    vx
    cA
    cF
    climeu
    @2
    @0
    cc
    wcel
    #
    @1
    wa
    #
    vx
    weu
    @3
    @1
    @5
    vx
    @1
    @4
    @0
    cF
    climcl
    pm4.71ri
    eubii
    @1
    vx
    cc
    df-reu
    bitr4i
    sylib
end
