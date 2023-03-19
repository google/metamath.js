include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "wb.mm"
include "eqcom.mm"
include "vex.mm"
include "opth.mm"
include "bitri.mm"
include "anbi12i.mm"
include "anbi1i.mm"
include "a1i.mm"
include "4exbidv.mm"
include "id.mm"
include "cgsex4g.mm"
include "bitrd.mm"

theorem copsex4g
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  assume copsex4g.1: |- ( ( ( x = A /\ y = B ) /\ ( z = C /\ w = D ) ) -> ( ph <-> ps ) )

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
  disjoint B x
  disjoint B y
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
  disjoint ps z
  disjoint ps w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint R w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint S w
  assert |- ( ( ( A e. R /\ B e. S ) /\ ( C e. R /\ D e. S ) ) -> ( E. x E. y E. z E. w ( ( <. A , B >. = <. x , y >. /\ <. C , D >. = <. z , w >. ) /\ ph ) <-> ps ) )

  proof
    cA
    cR
    wcel
    cB
    cS
    wcel
    wa
    cC
    cR
    wcel
    cD
    cS
    wcel
    wa
    wa
    #
    cA
    cB
    cop
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    cC
    cD
    cop
    #
    vz
    cv
    #
    vw
    cv
    #
    cop
    #
    wceq
    #
    wa
    #
    wph
    wa
    #
    vw
    wex
    vz
    wex
    vy
    wex
    vx
    wex
    @2
    cA
    wceq
    @3
    cB
    wceq
    wa
    #
    @7
    cC
    wceq
    @8
    cD
    wceq
    wa
    #
    wa
    #
    wph
    wa
    #
    vw
    wex
    vz
    wex
    vy
    wex
    vx
    wex
    wps
    @0
    @12
    @16
    vx
    vy
    vz
    vw
    @12
    @16
    wb
    @0
    @11
    @15
    wph
    @5
    @13
    @10
    @14
    @5
    @4
    @1
    wceq
    @13
    @1
    @4
    eqcom
    @2
    @3
    cA
    cB
    vx
    vex
    vy
    vex
    opth
    bitri
    @10
    @9
    @6
    wceq
    @14
    @6
    @9
    eqcom
    @7
    @8
    cC
    cD
    vz
    vex
    vw
    vex
    opth
    bitri
    anbi12i
    anbi1i
    a1i
    4exbidv
    wph
    wps
    @15
    vx
    vy
    vz
    vw
    cA
    cB
    cC
    cD
    cR
    cS
    @15
    id
    copsex4g.1
    cgsex4g
    bitrd
end
