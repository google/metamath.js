include "cst.mm"
include "wcel.mm"
include "cch.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "cfv.mm"
include "wi.mm"
include "chil.mm"
include "wceq.mm"
include "cv.mm"
include "cort.mm"
include "wss.mm"
include "chj.mm"
include "caddc.mm"
include "wral.mm"
include "isst.mm"
include "simp1bi.mm"
include "ffvelrn.mm"
include "ex.mm"
include "syl.mm"

theorem sticl
  let cA: class A
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let cB: class B


  assert |- ( S e. States -> ( A e. CH -> ( S ` A ) e. ( 0 [,] 1 ) ) )

  proof
    cS
    cst
    wcel
    #
    cch
    cc0
    c1
    cicc
    co
    #
    cS
    wf
    #
    cA
    cch
    wcel
    #
    cA
    cS
    cfv
    @1
    wcel
    #
    wi
    @0
    @2
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
    @5
    @6
    chj
    co
    cS
    cfv
    @5
    cS
    cfv
    @6
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
    simp1bi
    @2
    @3
    @4
    cch
    @1
    cA
    cS
    ffvelrn
    ex
    syl
end
