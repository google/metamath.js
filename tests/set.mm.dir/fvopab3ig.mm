include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cv.mm"
include "copab.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "opelopabg.mm"
include "biimpar.mm"
include "exp43.mm"
include "pm2.43a.mm"
include "imp.mm"
include "fveq1i.mm"
include "wfun.mm"
include "wmo.mm"
include "funopab.mm"
include "moanimv.mm"
include "mpbir.mm"
include "mpgbir.mm"
include "funopfv.mm"
include "ax-mp.mm"
include "syl5eq.mm"
include "syl6.mm"

theorem fvopab3ig
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  assume fvopab3ig.1: |- ( x = A -> ( ph <-> ps ) )
  assume fvopab3ig.2: |- ( y = B -> ( ps <-> ch ) )
  assume fvopab3ig.3: |- ( x e. C -> E* y ph )
  assume fvopab3ig.4: |- F = { <. x , y >. | ( x e. C /\ ph ) }

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint ch x
  disjoint ch y
  assert |- ( ( A e. C /\ B e. D ) -> ( ch -> ( F ` A ) = B ) )

  proof
    cA
    cC
    wcel
    #
    cB
    cD
    wcel
    #
    wa
    #
    wch
    cA
    cB
    cop
    vx
    cv
    #
    cC
    wcel
    #
    wph
    wa
    #
    vx
    vy
    copab
    #
    wcel
    #
    cA
    cF
    cfv
    #
    cB
    wceq
    @0
    @1
    wch
    @7
    wi
    #
    @1
    @0
    @9
    @0
    @1
    @0
    wch
    @7
    @2
    @7
    @0
    wch
    wa
    #
    @5
    @0
    wps
    wa
    @10
    vx
    vy
    cA
    cB
    cC
    cD
    @3
    cA
    wceq
    @4
    @0
    wph
    wps
    @3
    cA
    cC
    eleq1
    fvopab3ig.1
    anbi12d
    vy
    cv
    cB
    wceq
    wps
    wch
    @0
    fvopab3ig.2
    anbi2d
    opelopabg
    biimpar
    exp43
    pm2.43a
    imp
    @7
    @8
    cA
    @6
    cfv
    #
    cB
    cA
    cF
    @6
    fvopab3ig.4
    fveq1i
    @6
    wfun
    #
    @7
    @11
    cB
    wceq
    wi
    @12
    @5
    vy
    wmo
    #
    vx
    @5
    vx
    vy
    funopab
    @13
    @4
    wph
    vy
    wmo
    wi
    fvopab3ig.3
    @4
    wph
    vy
    moanimv
    mpbir
    mpgbir
    cA
    cB
    @6
    funopfv
    ax-mp
    syl5eq
    syl6
end
