include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "imbi12d.mm"
include "anbi2d.mm"
include "vtocl4g.mm"
include "pm2.43i.mm"

theorem vtocl4ga
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
  assume vtocl4ga.5: |- ( ( ( x e. Q /\ y e. R ) /\ ( z e. S /\ w e. T ) ) -> ph )

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
    cA
    cQ
    wcel
    #
    cB
    cR
    wcel
    #
    wa
    #
    cC
    cS
    wcel
    #
    cD
    cT
    wcel
    #
    wa
    #
    wa
    #
    wth
    vx
    cv
    #
    cQ
    wcel
    #
    vy
    cv
    #
    cR
    wcel
    #
    wa
    #
    vz
    cv
    #
    cS
    wcel
    #
    vw
    cv
    #
    cT
    wcel
    #
    wa
    #
    wa
    #
    wph
    wi
    @0
    @10
    wa
    #
    @16
    wa
    #
    wps
    wi
    @2
    @16
    wa
    #
    wch
    wi
    @6
    wth
    wi
    @2
    @3
    @15
    wa
    #
    wa
    #
    wrh
    wi
    vx
    vy
    vz
    vw
    cA
    cB
    cC
    cD
    cQ
    cR
    cS
    cT
    @7
    cA
    wceq
    #
    @17
    @19
    wph
    wps
    @23
    @11
    @18
    @16
    @23
    @8
    @0
    @10
    @7
    cA
    cQ
    eleq1
    anbi1d
    anbi1d
    vtocl4ga.1
    imbi12d
    @9
    cB
    wceq
    #
    @19
    @20
    wps
    wch
    @24
    @18
    @2
    @16
    @24
    @10
    @1
    @0
    @9
    cB
    cR
    eleq1
    anbi2d
    anbi1d
    vtocl4ga.2
    imbi12d
    @12
    cC
    wceq
    #
    @20
    @22
    wch
    wrh
    @25
    @16
    @21
    @2
    @25
    @13
    @3
    @15
    @12
    cC
    cS
    eleq1
    anbi1d
    anbi2d
    vtocl4ga.3
    imbi12d
    @14
    cD
    wceq
    #
    @22
    @6
    wrh
    wth
    @26
    @21
    @5
    @2
    @26
    @15
    @4
    @3
    @14
    cD
    cT
    eleq1
    anbi2d
    anbi2d
    vtocl4ga.4
    imbi12d
    vtocl4ga.5
    vtocl4g
    pm2.43i
end
