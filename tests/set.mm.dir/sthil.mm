include "cst.mm"
include "wcel.mm"
include "cch.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "chil.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cort.mm"
include "wss.mm"
include "chj.mm"
include "caddc.mm"
include "wi.mm"
include "wral.mm"
include "isst.mm"
include "simp2bi.mm"

theorem sthil
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let cB: class B


  assert |- ( S e. States -> ( S ` ~H ) = 1 )

  proof
    cS
    cst
    wcel
    cch
    cc0
    c1
    cicc
    co
    cS
    wf
    chil
    cS
    cfv
    c1
    wceq
    vx
    cv
    #
    vy
    cv
    #
    cort
    cfv
    wss
    @0
    @1
    chj
    co
    cS
    cfv
    @0
    cS
    cfv
    @1
    cS
    cfv
    caddc
    co
    wceq
    wi
    vy
    cch
    wral
    vx
    cch
    wral
    vx
    vy
    cS
    isst
    simp2bi
end
