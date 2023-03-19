include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "cres.mm"
include "resopab.mm"
include "ssel.mm"
include "pm4.71d.mm"
include "anbi1d.mm"
include "anass.mm"
include "syl6rbb.mm"
include "opabbidv.mm"
include "syl5eq.mm"

theorem resopab2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C y
  assert |- ( A C_ B -> ( { <. x , y >. | ( x e. B /\ ph ) } |` A ) = { <. x , y >. | ( x e. A /\ ph ) } )

  proof
    cA
    cB
    wss
    #
    vx
    cv
    #
    cB
    wcel
    #
    wph
    wa
    #
    vx
    vy
    copab
    cA
    cres
    @1
    cA
    wcel
    #
    @3
    wa
    #
    vx
    vy
    copab
    @4
    wph
    wa
    #
    vx
    vy
    copab
    @3
    vx
    vy
    cA
    resopab
    @0
    @5
    @6
    vx
    vy
    @0
    @6
    @4
    @2
    wa
    #
    wph
    wa
    @5
    @0
    @4
    @7
    wph
    @0
    @4
    @2
    cA
    cB
    @1
    ssel
    pm4.71d
    anbi1d
    @4
    @2
    wph
    anass
    syl6rbb
    opabbidv
    syl5eq
end
