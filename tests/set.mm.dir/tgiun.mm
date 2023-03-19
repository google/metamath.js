include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "ciun.mm"
include "cmpt.mm"
include "crn.mm"
include "cuni.mm"
include "ctg.mm"
include "cfv.mm"
include "wceq.mm"
include "dfiun3g.mm"
include "adantl.mm"
include "wss.mm"
include "eqid.mm"
include "rnmptss.mm"
include "eltg3i.mm"
include "sylan2.mm"
include "eqeltrd.mm"

theorem tgiun
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint B x
  disjoint V x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint V y
  disjoint V z
  assert |- ( ( B e. V /\ A. x e. A C e. B ) -> U_ x e. A C e. ( topGen ` B ) )

  proof
    cB
    cV
    wcel
    #
    cC
    cB
    wcel
    vx
    cA
    wral
    #
    wa
    vx
    cA
    cC
    ciun
    #
    vx
    cA
    cC
    cmpt
    #
    crn
    #
    cuni
    #
    cB
    ctg
    cfv
    #
    @1
    @2
    @5
    wceq
    @0
    vx
    cA
    cC
    cB
    dfiun3g
    adantl
    @1
    @0
    @4
    cB
    wss
    @5
    @6
    wcel
    vx
    cA
    cC
    cB
    @3
    @3
    eqid
    rnmptss
    @4
    cB
    cV
    eltg3i
    sylan2
    eqeltrd
end
