include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "imbi2d.mm"
include "3expia.mm"
include "2optocl.mm"
include "com12.mm"
include "optocl.mm"
include "impcom.mm"
include "3impa.mm"

theorem 3optocl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cF: class F
  assume 3optocl.1: |- R = ( D X. F )
  assume 3optocl.2: |- ( <. x , y >. = A -> ( ph <-> ps ) )
  assume 3optocl.3: |- ( <. z , w >. = B -> ( ps <-> ch ) )
  assume 3optocl.4: |- ( <. v , u >. = C -> ( ch <-> th ) )
  assume 3optocl.5: |- ( ( ( x e. D /\ y e. F ) /\ ( z e. D /\ w e. F ) /\ ( v e. D /\ u e. F ) ) -> ph )

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint A x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint A y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint A z
  disjoint v w
  disjoint u w
  disjoint A w
  disjoint u v
  disjoint A v
  disjoint A u
  disjoint B z
  disjoint B w
  disjoint B v
  disjoint B u
  disjoint C v
  disjoint C u
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint D w
  disjoint D v
  disjoint D u
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint F w
  disjoint F v
  disjoint F u
  disjoint R z
  disjoint R w
  disjoint R v
  disjoint R u
  disjoint ps x
  disjoint ps y
  disjoint ch z
  disjoint ch w
  disjoint th v
  disjoint th u
  assert |- ( ( A e. R /\ B e. R /\ C e. R ) -> th )

  proof
    cA
    cR
    wcel
    #
    cB
    cR
    wcel
    #
    cC
    cR
    wcel
    #
    wth
    @2
    @0
    @1
    wa
    #
    wth
    @3
    wch
    wi
    @3
    wth
    wi
    vv
    vu
    cC
    cD
    cF
    cR
    3optocl.1
    vv
    cv
    #
    vu
    cv
    #
    cop
    cC
    wceq
    wch
    wth
    @3
    3optocl.4
    imbi2d
    @3
    @4
    cD
    wcel
    @5
    cF
    wcel
    wa
    #
    wch
    @6
    wph
    wi
    @6
    wps
    wi
    @6
    wch
    wi
    vx
    vy
    vz
    vw
    cA
    cB
    cD
    cF
    cR
    3optocl.1
    vx
    cv
    #
    vy
    cv
    #
    cop
    cA
    wceq
    wph
    wps
    @6
    3optocl.2
    imbi2d
    vz
    cv
    #
    vw
    cv
    #
    cop
    cB
    wceq
    wps
    wch
    @6
    3optocl.3
    imbi2d
    @7
    cD
    wcel
    @8
    cF
    wcel
    wa
    @9
    cD
    wcel
    @10
    cF
    wcel
    wa
    @6
    wph
    3optocl.5
    3expia
    2optocl
    com12
    optocl
    impcom
    3impa
end
