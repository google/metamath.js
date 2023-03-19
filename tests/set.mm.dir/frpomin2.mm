include "wfr.mm"
include "wpo.mm"
include "wse.mm"
include "w3a.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "cpred.mm"
include "wceq.mm"
include "frpomin.mm"
include "crab.mm"
include "vex.mm"
include "dfpred3.mm"
include "eqeq1i.mm"
include "rabeq0.mm"
include "bitri.mm"
include "rexbii.mm"
include "sylibr.mm"

theorem frpomin2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint A x
  disjoint R x
  disjoint B x
  disjoint A y
  disjoint A z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint R y
  disjoint R z
  disjoint R w
  disjoint B y
  disjoint B z
  disjoint B w
  assert |- ( ( ( R Fr A /\ R Po A /\ R Se A ) /\ ( B C_ A /\ B =/= (/) ) ) -> E. x e. B Pred ( R , B , x ) = (/) )

  proof
    cA
    cR
    wfr
    cA
    cR
    wpo
    cA
    cR
    wse
    w3a
    cB
    cA
    wss
    cB
    c0
    wne
    wa
    wa
    vy
    cv
    vx
    cv
    #
    cR
    wbr
    #
    wn
    vy
    cB
    wral
    #
    vx
    cB
    wrex
    cB
    cR
    @0
    cpred
    #
    c0
    wceq
    #
    vx
    cB
    wrex
    vx
    vy
    cA
    cB
    cR
    frpomin
    @4
    @2
    vx
    cB
    @4
    @1
    vy
    cB
    crab
    #
    c0
    wceq
    @2
    @3
    @5
    c0
    vy
    cB
    cR
    @0
    vx
    vex
    dfpred3
    eqeq1i
    @1
    vy
    cB
    rabeq0
    bitri
    rexbii
    sylibr
end
