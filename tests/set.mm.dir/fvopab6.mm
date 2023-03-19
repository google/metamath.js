include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cvv.mm"
include "wi.mm"
include "elex.mm"
include "cv.mm"
include "wa.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "iba.mm"
include "bicomd.mm"
include "wmo.mm"
include "moeq.mm"
include "moani.mm"
include "a1i.mm"
include "copab.mm"
include "vex.mm"
include "biantrur.mm"
include "opabbii.mm"
include "eqtri.mm"
include "fvopab3ig.mm"
include "sylan.mm"
include "3impia.mm"

theorem fvopab6
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cF: class F
  assume fvopab6.1: |- F = { <. x , y >. | ( ph /\ y = B ) }
  assume fvopab6.2: |- ( x = A -> ( ph <-> ps ) )
  assume fvopab6.3: |- ( x = A -> B = C )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint ps x
  disjoint ps y
  disjoint B y
  disjoint C x
  disjoint C y
  assert |- ( ( A e. D /\ C e. R /\ ps ) -> ( F ` A ) = C )

  proof
    cA
    cD
    wcel
    #
    cC
    cR
    wcel
    #
    wps
    cA
    cF
    cfv
    cC
    wceq
    #
    @0
    cA
    cvv
    wcel
    @1
    wps
    @2
    wi
    cA
    cD
    elex
    wph
    vy
    cv
    #
    cB
    wceq
    #
    wa
    #
    wps
    @3
    cC
    wceq
    #
    wa
    #
    wps
    vx
    vy
    cA
    cC
    cvv
    cR
    cF
    vx
    cv
    #
    cA
    wceq
    #
    wph
    wps
    @4
    @6
    fvopab6.2
    @9
    cB
    cC
    @3
    fvopab6.3
    eqeq2d
    anbi12d
    @6
    wps
    @7
    @6
    wps
    iba
    bicomd
    @5
    vy
    wmo
    @8
    cvv
    wcel
    #
    @4
    wph
    vy
    vy
    cB
    moeq
    moani
    a1i
    cF
    @5
    vx
    vy
    copab
    @10
    @5
    wa
    #
    vx
    vy
    copab
    fvopab6.1
    @5
    @11
    vx
    vy
    @10
    @5
    vx
    vex
    biantrur
    opabbii
    eqtri
    fvopab3ig
    sylan
    3impia
end
