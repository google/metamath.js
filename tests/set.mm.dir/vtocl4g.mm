include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "cv.mm"
include "wceq.mm"
include "imbi2d.mm"
include "vtocl2g.mm"
include "impcom.mm"

theorem vtocl4g
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wrh: wff rh
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  assume vtocl4ga.1: |- ( x = A -> ( ph <-> ps ) )
  assume vtocl4ga.2: |- ( y = B -> ( ps <-> ch ) )
  assume vtocl4ga.3: |- ( z = C -> ( ch <-> rh ) )
  assume vtocl4ga.4: |- ( w = D -> ( rh <-> th ) )
  assume vtocl4g.5: |- ph

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint C w
  disjoint C z
  disjoint D w
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint T w
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint Q w
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint ps x
  disjoint rh z
  disjoint th w
  disjoint ch y
  assert |- ( ( ( A e. Q /\ B e. R ) /\ ( C e. S /\ D e. T ) ) -> th )

  proof
    cC
    cS
    wcel
    cD
    cT
    wcel
    wa
    cA
    cQ
    wcel
    cB
    cR
    wcel
    wa
    #
    wth
    @0
    wch
    wi
    @0
    wrh
    wi
    @0
    wth
    wi
    vz
    vw
    cC
    cD
    cS
    cT
    vz
    cv
    cC
    wceq
    wch
    wrh
    @0
    vtocl4ga.3
    imbi2d
    vw
    cv
    cD
    wceq
    wrh
    wth
    @0
    vtocl4ga.4
    imbi2d
    wph
    wps
    wch
    vx
    vy
    cA
    cB
    cQ
    cR
    vtocl4ga.1
    vtocl4ga.2
    vtocl4g.5
    vtocl2g
    vtocl2g
    impcom
end
