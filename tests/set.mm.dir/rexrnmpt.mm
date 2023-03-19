include "wcel.mm"
include "wral.mm"
include "wn.mm"
include "crn.mm"
include "wrex.mm"
include "cv.mm"
include "wceq.mm"
include "notbid.mm"
include "ralrnmpt.mm"
include "dfrex2.mm"
include "3bitr4g.mm"

theorem rexrnmpt
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let vw: setvar w
  let vz: setvar z
  assume ralrnmpt.1: |- F = ( x e. A |-> B )
  assume ralrnmpt.2: |- ( y = B -> ( ps <-> ch ) )

  disjoint A x
  disjoint B y
  disjoint ch y
  disjoint F y
  disjoint ps x
  disjoint w x
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A z
  disjoint w y
  disjoint F w
  disjoint y z
  disjoint F z
  disjoint ps w
  disjoint ps z
  assert |- ( A. x e. A B e. V -> ( E. y e. ran F ps <-> E. x e. A ch ) )

  proof
    cB
    cV
    wcel
    vx
    cA
    wral
    #
    wps
    wn
    #
    vy
    cF
    crn
    #
    wral
    #
    wn
    wch
    wn
    #
    vx
    cA
    wral
    #
    wn
    wps
    vy
    @2
    wrex
    wch
    vx
    cA
    wrex
    @0
    @3
    @5
    @1
    @4
    vx
    vy
    cA
    cB
    cF
    cV
    ralrnmpt.1
    vy
    cv
    cB
    wceq
    wps
    wch
    ralrnmpt.2
    notbid
    ralrnmpt
    notbid
    wps
    vy
    @2
    dfrex2
    wch
    vx
    cA
    dfrex2
    3bitr4g
end
