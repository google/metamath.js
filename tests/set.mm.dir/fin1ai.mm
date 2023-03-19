include "cfin1a.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cfn.mm"
include "cdif.mm"
include "wo.mm"
include "cpw.mm"
include "wceq.mm"
include "eleq1.mm"
include "difeq2.mm"
include "eleq1d.mm"
include "orbi12d.mm"
include "wral.mm"
include "isfin1a.mm"
include "ibi.mm"
include "adantr.mm"
include "elpw2g.mm"
include "biimpar.mm"
include "rspcdva.mm"

theorem fin1ai
  let cA: class A
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( ( A e. Fin1a /\ X C_ A ) -> ( X e. Fin \/ ( A \ X ) e. Fin ) )

  proof
    cA
    cfin1a
    wcel
    #
    cX
    cA
    wss
    #
    wa
    vx
    cv
    #
    cfn
    wcel
    #
    cA
    @2
    cdif
    #
    cfn
    wcel
    #
    wo
    #
    cX
    cfn
    wcel
    #
    cA
    cX
    cdif
    #
    cfn
    wcel
    #
    wo
    vx
    cA
    cpw
    #
    cX
    @2
    cX
    wceq
    #
    @3
    @7
    @5
    @9
    @2
    cX
    cfn
    eleq1
    @11
    @4
    @8
    cfn
    @2
    cX
    cA
    difeq2
    eleq1d
    orbi12d
    @0
    @6
    vx
    @10
    wral
    #
    @1
    @0
    @12
    vx
    cA
    cfin1a
    isfin1a
    ibi
    adantr
    @0
    cX
    @10
    wcel
    @1
    cX
    cA
    cfin1a
    elpw2g
    biimpar
    rspcdva
end
