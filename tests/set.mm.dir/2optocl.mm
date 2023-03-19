include "wcel.mm"
include "wi.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "imbi2d.mm"
include "wa.mm"
include "ex.mm"
include "optocl.mm"
include "com12.mm"
include "impcom.mm"

theorem 2optocl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  assume 2optocl.1: |- R = ( C X. D )
  assume 2optocl.2: |- ( <. x , y >. = A -> ( ph <-> ps ) )
  assume 2optocl.3: |- ( <. z , w >. = B -> ( ps <-> ch ) )
  assume 2optocl.4: |- ( ( ( x e. C /\ y e. D ) /\ ( z e. C /\ w e. D ) ) -> ph )

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint A x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B z
  disjoint B w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint C w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint D w
  disjoint ps x
  disjoint ps y
  disjoint ch z
  disjoint ch w
  disjoint R z
  disjoint R w
  assert |- ( ( A e. R /\ B e. R ) -> ch )

  proof
    cB
    cR
    wcel
    cA
    cR
    wcel
    #
    wch
    @0
    wps
    wi
    @0
    wch
    wi
    vz
    vw
    cB
    cC
    cD
    cR
    2optocl.1
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
    @0
    2optocl.3
    imbi2d
    @0
    @1
    cC
    wcel
    @2
    cD
    wcel
    wa
    #
    wps
    @3
    wph
    wi
    @3
    wps
    wi
    vx
    vy
    cA
    cC
    cD
    cR
    2optocl.1
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
    @3
    2optocl.2
    imbi2d
    @4
    cC
    wcel
    @5
    cD
    wcel
    wa
    @3
    wph
    2optocl.4
    ex
    optocl
    com12
    optocl
    impcom
end
