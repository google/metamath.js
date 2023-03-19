include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wex.mm"
include "df-rex.mm"
include "bitri.mm"
include "imbi2d.mm"
include "3expia.mm"
include "2gencl.mm"
include "com12.mm"
include "gencl.mm"
include "3impia.mm"

theorem 3gencl
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
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  assume 3gencl.1: |- ( D e. S <-> E. x e. R A = D )
  assume 3gencl.2: |- ( F e. S <-> E. y e. R B = F )
  assume 3gencl.3: |- ( G e. S <-> E. z e. R C = G )
  assume 3gencl.4: |- ( A = D -> ( ph <-> ps ) )
  assume 3gencl.5: |- ( B = F -> ( ps <-> ch ) )
  assume 3gencl.6: |- ( C = G -> ( ch <-> th ) )
  assume 3gencl.7: |- ( ( x e. R /\ y e. R /\ z e. R ) -> ph )

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint F z
  disjoint R x
  disjoint R y
  disjoint S y
  disjoint S z
  disjoint ps x
  disjoint ch y
  disjoint th z
  assert |- ( ( D e. S /\ F e. S /\ G e. S ) -> th )

  proof
    cD
    cS
    wcel
    #
    cF
    cS
    wcel
    #
    cG
    cS
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
    vz
    cv
    cR
    wcel
    #
    @2
    vz
    cC
    cG
    @2
    cC
    cG
    wceq
    #
    vz
    cR
    wrex
    @4
    @5
    wa
    vz
    wex
    3gencl.3
    @5
    vz
    cR
    df-rex
    bitri
    @5
    wch
    wth
    @3
    3gencl.6
    imbi2d
    @3
    @4
    wch
    @4
    wph
    wi
    @4
    wps
    wi
    @4
    wch
    wi
    vx
    vy
    cA
    cB
    cD
    cF
    cR
    cS
    3gencl.1
    3gencl.2
    cA
    cD
    wceq
    wph
    wps
    @4
    3gencl.4
    imbi2d
    cB
    cF
    wceq
    wps
    wch
    @4
    3gencl.5
    imbi2d
    vx
    cv
    cR
    wcel
    vy
    cv
    cR
    wcel
    @4
    wph
    3gencl.7
    3expia
    2gencl
    com12
    gencl
    com12
    3impia
end
