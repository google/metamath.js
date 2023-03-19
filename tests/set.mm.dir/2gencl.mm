include "wcel.mm"
include "wi.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "wex.mm"
include "df-rex.mm"
include "bitri.mm"
include "imbi2d.mm"
include "ex.mm"
include "gencl.mm"
include "com12.mm"
include "impcom.mm"

theorem 2gencl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  assume 2gencl.1: |- ( C e. S <-> E. x e. R A = C )
  assume 2gencl.2: |- ( D e. S <-> E. y e. R B = D )
  assume 2gencl.3: |- ( A = C -> ( ph <-> ps ) )
  assume 2gencl.4: |- ( B = D -> ( ps <-> ch ) )
  assume 2gencl.5: |- ( ( x e. R /\ y e. R ) -> ph )

  disjoint x y
  disjoint R x
  disjoint ps x
  disjoint C y
  disjoint S y
  disjoint ch y
  assert |- ( ( C e. S /\ D e. S ) -> ch )

  proof
    cD
    cS
    wcel
    #
    cC
    cS
    wcel
    #
    wch
    @1
    wps
    wi
    @1
    wch
    wi
    vy
    cv
    cR
    wcel
    #
    @0
    vy
    cB
    cD
    @0
    cB
    cD
    wceq
    #
    vy
    cR
    wrex
    @2
    @3
    wa
    vy
    wex
    2gencl.2
    @3
    vy
    cR
    df-rex
    bitri
    @3
    wps
    wch
    @1
    2gencl.4
    imbi2d
    @1
    @2
    wps
    @2
    wph
    wi
    @2
    wps
    wi
    vx
    cv
    cR
    wcel
    #
    @1
    vx
    cA
    cC
    @1
    cA
    cC
    wceq
    #
    vx
    cR
    wrex
    @4
    @5
    wa
    vx
    wex
    2gencl.1
    @5
    vx
    cR
    df-rex
    bitri
    @5
    wph
    wps
    @2
    2gencl.3
    imbi2d
    @4
    @2
    wph
    2gencl.5
    ex
    gencl
    com12
    gencl
    impcom
end
