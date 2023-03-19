include "wcel.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "ralbidv.mm"
include "rspc2v.mm"
include "rspcv.mm"
include "sylan9.mm"
include "3impa.mm"

theorem rspc3v
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cT: class T
  assume rspc3v.1: |- ( x = A -> ( ph <-> ch ) )
  assume rspc3v.2: |- ( y = B -> ( ch <-> th ) )
  assume rspc3v.3: |- ( z = C -> ( th <-> ps ) )

  disjoint ps z
  disjoint ch x
  disjoint th y
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C z
  disjoint R x
  disjoint S x
  disjoint S y
  disjoint T x
  disjoint T y
  disjoint T z
  assert |- ( ( A e. R /\ B e. S /\ C e. T ) -> ( A. x e. R A. y e. S A. z e. T ph -> ps ) )

  proof
    cA
    cR
    wcel
    #
    cB
    cS
    wcel
    #
    cC
    cT
    wcel
    #
    wph
    vz
    cT
    wral
    #
    vy
    cS
    wral
    vx
    cR
    wral
    #
    wps
    wi
    @0
    @1
    wa
    @4
    wth
    vz
    cT
    wral
    #
    @2
    wps
    @3
    @5
    wch
    vz
    cT
    wral
    vx
    vy
    cA
    cB
    cR
    cS
    vx
    cv
    cA
    wceq
    wph
    wch
    vz
    cT
    rspc3v.1
    ralbidv
    vy
    cv
    cB
    wceq
    wch
    wth
    vz
    cT
    rspc3v.2
    ralbidv
    rspc2v
    wth
    wps
    vz
    cC
    cT
    rspc3v.3
    rspcv
    sylan9
    3impa
end
