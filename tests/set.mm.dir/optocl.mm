include "cxp.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "elxp3.mm"
include "opelxp.mm"
include "sylbi.mm"
include "syl5ib.mm"
include "imp.mm"
include "exlimivv.mm"
include "eleq2s.mm"

theorem optocl
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume optocl.1: |- D = ( B X. C )
  assume optocl.2: |- ( <. x , y >. = A -> ( ph <-> ps ) )
  assume optocl.3: |- ( ( x e. B /\ y e. C ) -> ph )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint ps x
  disjoint ps y
  assert |- ( A e. D -> ps )

  proof
    wps
    cA
    cB
    cC
    cxp
    #
    cD
    cA
    @0
    wcel
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cA
    wceq
    #
    @3
    @0
    wcel
    #
    wa
    #
    vy
    wex
    vx
    wex
    wps
    vx
    vy
    cA
    cB
    cC
    elxp3
    @6
    wps
    vx
    vy
    @4
    @5
    wps
    @5
    wph
    @4
    wps
    @5
    @1
    cB
    wcel
    @2
    cC
    wcel
    wa
    wph
    @1
    @2
    cB
    cC
    opelxp
    optocl.3
    sylbi
    optocl.2
    syl5ib
    imp
    exlimivv
    sylbi
    optocl.1
    eleq2s
end
