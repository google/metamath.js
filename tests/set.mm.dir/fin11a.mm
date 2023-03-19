include "cfn.mm"
include "wcel.mm"
include "cfin1a.mm"
include "cv.mm"
include "cdif.mm"
include "wo.mm"
include "cpw.mm"
include "wral.mm"
include "wa.mm"
include "wss.mm"
include "elpwi.mm"
include "ssfi.mm"
include "sylan2.mm"
include "orcd.mm"
include "ralrimiva.mm"
include "isfin1a.mm"
include "mpbird.mm"

theorem fin11a
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cV: class V


  assert |- ( A e. Fin -> A e. Fin1a )

  proof
    cA
    cfn
    wcel
    #
    cA
    cfin1a
    wcel
    vx
    cv
    #
    cfn
    wcel
    #
    cA
    @1
    cdif
    cfn
    wcel
    #
    wo
    #
    vx
    cA
    cpw
    #
    wral
    @0
    @4
    vx
    @5
    @0
    @1
    @5
    wcel
    #
    wa
    @2
    @3
    @6
    @0
    @1
    cA
    wss
    @2
    @1
    cA
    elpwi
    cA
    @1
    ssfi
    sylan2
    orcd
    ralrimiva
    vx
    cA
    cfn
    isfin1a
    mpbird
end
