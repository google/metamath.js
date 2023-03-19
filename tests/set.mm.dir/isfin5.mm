include "cfin5.mm"
include "wcel.mm"
include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "ccda.mm"
include "co.mm"
include "csdm.mm"
include "wbr.mm"
include "wo.mm"
include "cab.mm"
include "df-fin5.mm"
include "eleq2i.mm"
include "cvv.mm"
include "id.mm"
include "0ex.mm"
include "syl6eqel.mm"
include "relsdom.mm"
include "brrelexi.mm"
include "jaoi.mm"
include "eqeq1.mm"
include "oveq12d.mm"
include "breq12d.mm"
include "orbi12d.mm"
include "elab3.mm"
include "bitri.mm"

theorem isfin5
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cX: class X


  assert |- ( A e. Fin5 <-> ( A = (/) \/ A ~< ( A +c A ) ) )

  proof
    cA
    cfin5
    wcel
    cA
    vx
    cv
    #
    c0
    wceq
    #
    @0
    @0
    @0
    ccda
    co
    #
    csdm
    wbr
    #
    wo
    #
    vx
    cab
    #
    wcel
    cA
    c0
    wceq
    #
    cA
    cA
    cA
    ccda
    co
    #
    csdm
    wbr
    #
    wo
    #
    cfin5
    @5
    cA
    vx
    df-fin5
    eleq2i
    @4
    @9
    vx
    cA
    @6
    cA
    cvv
    wcel
    @8
    @6
    cA
    c0
    cvv
    @6
    id
    0ex
    syl6eqel
    cA
    @7
    csdm
    relsdom
    brrelexi
    jaoi
    @0
    cA
    wceq
    #
    @1
    @6
    @3
    @8
    @0
    cA
    c0
    eqeq1
    @10
    @0
    cA
    @2
    @7
    csdm
    @10
    id
    #
    @10
    @0
    cA
    @0
    cA
    ccda
    @11
    @11
    oveq12d
    breq12d
    orbi12d
    elab3
    bitri
end
