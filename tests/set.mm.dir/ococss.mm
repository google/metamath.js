include "chil.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "ssel.mm"
include "ocorth.mm"
include "expd.mm"
include "ralrimdv.mm"
include "jcad.mm"
include "wb.mm"
include "ocss.mm"
include "ocel.mm"
include "syl.mm"
include "sylibrd.mm"
include "ssrdv.mm"

theorem ococss
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cH: class H
  let cB: class B


  assert |- ( A C_ ~H -> A C_ ( _|_ ` ( _|_ ` A ) ) )

  proof
    cA
    chil
    wss
    #
    vy
    cA
    cA
    cort
    cfv
    #
    cort
    cfv
    #
    @0
    vy
    cv
    #
    cA
    wcel
    #
    @3
    chil
    wcel
    #
    @3
    vx
    cv
    #
    csp
    co
    cc0
    wceq
    #
    vx
    @1
    wral
    #
    wa
    #
    @3
    @2
    wcel
    #
    @0
    @4
    @5
    @8
    cA
    chil
    @3
    ssel
    @0
    @4
    @7
    vx
    @1
    @0
    @4
    @6
    @1
    wcel
    @7
    @3
    @6
    cA
    ocorth
    expd
    ralrimdv
    jcad
    @0
    @1
    chil
    wss
    @10
    @9
    wb
    cA
    ocss
    vx
    @3
    @1
    ocel
    syl
    sylibrd
    ssrdv
end
