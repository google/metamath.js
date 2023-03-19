include "cc.mm"
include "wf.mm"
include "wcel.mm"
include "w3a.mm"
include "cc0.mm"
include "csupp.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cdiv.mm"
include "cfdiv.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "fdivmpt.mm"
include "adantr.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "adantl.mm"
include "simpr.mm"
include "ovexd.mm"
include "fvmptd.mm"

theorem fdivmptfv
  let cA: class A
  let cF: class F
  let cG: class G
  let cV: class V
  let cX: class X
  let vx: setvar x
  let vk: setvar k


  assert |- ( ( ( F : A --> CC /\ G : A --> CC /\ A e. V ) /\ X e. ( G supp 0 ) ) -> ( ( F /_f G ) ` X ) = ( ( F ` X ) / ( G ` X ) ) )

  proof
    cA
    cc
    cF
    wf
    cA
    cc
    cG
    wf
    cA
    cV
    wcel
    w3a
    #
    cX
    cG
    cc0
    csupp
    co
    #
    wcel
    #
    wa
    #
    vx
    cX
    vx
    cv
    #
    cF
    cfv
    #
    @4
    cG
    cfv
    #
    cdiv
    co
    #
    cX
    cF
    cfv
    #
    cX
    cG
    cfv
    #
    cdiv
    co
    #
    @1
    cF
    cG
    cfdiv
    co
    #
    cvv
    @0
    @11
    vx
    @1
    @7
    cmpt
    wceq
    @2
    vx
    cA
    cF
    cG
    cV
    fdivmpt
    adantr
    @4
    cX
    wceq
    #
    @7
    @10
    wceq
    @3
    @12
    @5
    @8
    @6
    @9
    cdiv
    @4
    cX
    cF
    fveq2
    @4
    cX
    cG
    fveq2
    oveq12d
    adantl
    @0
    @2
    simpr
    @3
    @8
    @9
    cdiv
    ovexd
    fvmptd
end
