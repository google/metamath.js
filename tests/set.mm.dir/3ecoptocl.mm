include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "cv.mm"
include "cop.mm"
include "cec.mm"
include "wceq.mm"
include "imbi2d.mm"
include "3expib.mm"
include "ecoptocl.mm"
include "com12.mm"
include "2ecoptocl.mm"
include "3impib.mm"

theorem 3ecoptocl
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
  let cS: class S
  assume 3ecoptocl.1: |- S = ( ( D X. D ) /. R )
  assume 3ecoptocl.2: |- ( [ <. x , y >. ] R = A -> ( ph <-> ps ) )
  assume 3ecoptocl.3: |- ( [ <. z , w >. ] R = B -> ( ps <-> ch ) )
  assume 3ecoptocl.4: |- ( [ <. v , u >. ] R = C -> ( ch <-> th ) )
  assume 3ecoptocl.5: |- ( ( ( x e. D /\ y e. D ) /\ ( z e. D /\ w e. D ) /\ ( v e. D /\ u e. D ) ) -> ph )

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
  disjoint S z
  disjoint S w
  disjoint S v
  disjoint S u
  disjoint R x
  disjoint R y
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
  assert |- ( ( A e. S /\ B e. S /\ C e. S ) -> th )

  proof
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    cC
    cS
    wcel
    #
    wth
    @1
    @2
    wa
    @0
    wth
    @0
    wps
    wi
    @0
    wch
    wi
    @0
    wth
    wi
    vz
    vw
    vv
    vu
    cB
    cC
    cD
    cD
    cR
    cS
    3ecoptocl.1
    vz
    cv
    #
    vw
    cv
    #
    cop
    cR
    cec
    cB
    wceq
    wps
    wch
    @0
    3ecoptocl.3
    imbi2d
    vv
    cv
    #
    vu
    cv
    #
    cop
    cR
    cec
    cC
    wceq
    wch
    wth
    @0
    3ecoptocl.4
    imbi2d
    @0
    @3
    cD
    wcel
    @4
    cD
    wcel
    wa
    #
    @5
    cD
    wcel
    @6
    cD
    wcel
    wa
    #
    wa
    #
    wps
    @9
    wph
    wi
    @9
    wps
    wi
    vx
    vy
    cA
    cD
    cD
    cR
    cS
    3ecoptocl.1
    vx
    cv
    #
    vy
    cv
    #
    cop
    cR
    cec
    cA
    wceq
    wph
    wps
    @9
    3ecoptocl.2
    imbi2d
    @10
    cD
    wcel
    @11
    cD
    wcel
    wa
    @7
    @8
    wph
    3ecoptocl.5
    3expib
    ecoptocl
    com12
    2ecoptocl
    com12
    3impib
end
