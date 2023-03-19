include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "weq.mm"
include "simpr.mm"
include "eleq12d.mm"
include "anbi12d.mm"
include "cbvexdva.mm"
include "df-rex.mm"
include "3bitr4g.mm"

theorem cbvrexdva2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume cbvraldva2.1: |- ( ( ph /\ x = y ) -> ( ps <-> ch ) )
  assume cbvraldva2.2: |- ( ( ph /\ x = y ) -> A = B )

  disjoint A y
  disjoint ps y
  disjoint B x
  disjoint ch x
  disjoint ph x
  disjoint x y
  disjoint ph y
  assert |- ( ph -> ( E. x e. A ps <-> E. y e. B ch ) )

  proof
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wps
    wa
    #
    vx
    wex
    vy
    cv
    #
    cB
    wcel
    #
    wch
    wa
    #
    vy
    wex
    wps
    vx
    cA
    wrex
    wch
    vy
    cB
    wrex
    wph
    @2
    @5
    vx
    vy
    wph
    vx
    vy
    weq
    #
    wa
    #
    @1
    @4
    wps
    wch
    @7
    @0
    @3
    cA
    cB
    wph
    @6
    simpr
    cbvraldva2.2
    eleq12d
    cbvraldva2.1
    anbi12d
    cbvexdva
    wps
    vx
    cA
    df-rex
    wch
    vy
    cB
    df-rex
    3bitr4g
end
