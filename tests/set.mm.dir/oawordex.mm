include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cv.mm"
include "coa.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wreu.mm"
include "oawordeu.mm"
include "ex.mm"
include "reurex.mm"
include "syl6.mm"
include "wi.mm"
include "oawordexr.mm"
include "adantr.mm"
include "impbid.mm"

theorem oawordex
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( ( A e. On /\ B e. On ) -> ( A C_ B <-> E. x e. On ( A +o x ) = B ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    wa
    #
    cA
    cB
    wss
    #
    cA
    vx
    cv
    coa
    co
    cB
    wceq
    #
    vx
    con0
    wrex
    #
    @2
    @3
    @4
    vx
    con0
    wreu
    #
    @5
    @2
    @3
    @6
    vx
    cA
    cB
    oawordeu
    ex
    @4
    vx
    con0
    reurex
    syl6
    @0
    @5
    @3
    wi
    @1
    @0
    @5
    @3
    vx
    cA
    cB
    oawordexr
    ex
    adantr
    impbid
end
