include "ciin.mm"
include "wcel.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "simpl.mm"
include "wb.mm"
include "eliin.mm"
include "adantr.mm"
include "mpbid.mm"
include "rspa.mm"
include "sylancom.mm"

theorem eliinid
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint A x
  assert |- ( ( A e. |^|_ x e. B C /\ x e. B ) -> A e. C )

  proof
    cA
    vx
    cB
    cC
    ciin
    #
    wcel
    #
    vx
    cv
    cB
    wcel
    #
    cA
    cC
    wcel
    #
    vx
    cB
    wral
    #
    @3
    @1
    @2
    wa
    @1
    @4
    @1
    @2
    simpl
    @1
    @1
    @4
    wb
    @2
    vx
    cA
    cB
    cC
    @0
    eliin
    adantr
    mpbid
    @3
    vx
    cB
    rspa
    sylancom
end
