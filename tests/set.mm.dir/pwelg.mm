include "cv.mm"
include "cuni.mm"
include "wcel.mm"
include "cpw.mm"
include "wa.mm"
include "wral.mm"
include "wi.mm"
include "simpr.mm"
include "ralimi.mm"
include "wceq.mm"
include "pweq.mm"
include "eleq1d.mm"
include "rspccv.mm"
include "syl.mm"
include "simpl.mm"
include "unieq.mm"
include "unipw.mm"
include "syl6eq.mm"
include "impbid.mm"

theorem pwelg
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A. x e. B ( U. x e. B /\ ~P x e. B ) -> ( A e. B <-> ~P A e. B ) )

  proof
    vx
    cv
    #
    cuni
    #
    cB
    wcel
    #
    @0
    cpw
    #
    cB
    wcel
    #
    wa
    #
    vx
    cB
    wral
    #
    cA
    cB
    wcel
    #
    cA
    cpw
    #
    cB
    wcel
    #
    @6
    @4
    vx
    cB
    wral
    @7
    @9
    wi
    @5
    @4
    vx
    cB
    @2
    @4
    simpr
    ralimi
    @4
    @9
    vx
    cA
    cB
    @0
    cA
    wceq
    @3
    @8
    cB
    @0
    cA
    pweq
    eleq1d
    rspccv
    syl
    @6
    @2
    vx
    cB
    wral
    @9
    @7
    wi
    @5
    @2
    vx
    cB
    @2
    @4
    simpl
    ralimi
    @2
    @7
    vx
    @8
    cB
    @0
    @8
    wceq
    #
    @1
    cA
    cB
    @10
    @1
    @8
    cuni
    cA
    @0
    @8
    unieq
    cA
    unipw
    syl6eq
    eleq1d
    rspccv
    syl
    impbid
end
