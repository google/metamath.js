include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "cxp.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "2exbidv.mm"
include "elabg.mm"
include "ibi.mm"
include "copab.mm"
include "df-xp.mm"
include "df-opab.mm"
include "eqtri.mm"
include "eleq2s.mm"

theorem elxpi
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  assert |- ( A e. ( B X. C ) -> E. x E. y ( A = <. x , y >. /\ ( x e. B /\ y e. C ) ) )

  proof
    cA
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
    @0
    cB
    wcel
    @1
    cC
    wcel
    wa
    #
    wa
    #
    vy
    wex
    vx
    wex
    #
    cA
    vz
    cv
    #
    @2
    wceq
    #
    @4
    wa
    #
    vy
    wex
    vx
    wex
    #
    vz
    cab
    #
    cB
    cC
    cxp
    #
    cA
    @11
    wcel
    @6
    @10
    @6
    vz
    cA
    @11
    @7
    cA
    wceq
    #
    @9
    @5
    vx
    vy
    @13
    @8
    @3
    @4
    @7
    cA
    @2
    eqeq1
    anbi1d
    2exbidv
    elabg
    ibi
    @12
    @4
    vx
    vy
    copab
    @11
    vx
    vy
    cB
    cC
    df-xp
    @4
    vx
    vy
    vz
    df-opab
    eqtri
    eleq2s
end
