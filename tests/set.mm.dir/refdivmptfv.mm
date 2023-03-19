include "cr.mm"
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
include "cc.mm"
include "id.mm"
include "wss.mm"
include "ax-resscn.mm"
include "a1i.mm"
include "fssd.mm"
include "3anim123i.mm"
include "fdivmpt.mm"
include "syl.mm"
include "adantr.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "adantl.mm"
include "simpr.mm"
include "ovexd.mm"
include "fvmptd.mm"

theorem refdivmptfv
  let cA: class A
  let cF: class F
  let cG: class G
  let cV: class V
  let cX: class X
  let vx: setvar x
  let vk: setvar k


  assert |- ( ( ( F : A --> RR /\ G : A --> RR /\ A e. V ) /\ X e. ( G supp 0 ) ) -> ( ( F /_f G ) ` X ) = ( ( F ` X ) / ( G ` X ) ) )

  proof
    cA
    cr
    cF
    wf
    #
    cA
    cr
    cG
    wf
    #
    cA
    cV
    wcel
    #
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
    @7
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
    @4
    cF
    cG
    cfdiv
    co
    #
    cvv
    @3
    @14
    vx
    @4
    @10
    cmpt
    wceq
    #
    @5
    @3
    cA
    cc
    cF
    wf
    #
    cA
    cc
    cG
    wf
    #
    @2
    w3a
    @15
    @0
    @16
    @1
    @17
    @2
    @2
    @0
    cA
    cr
    cc
    cF
    @0
    id
    cr
    cc
    wss
    #
    @0
    ax-resscn
    a1i
    fssd
    @1
    cA
    cr
    cc
    cG
    @1
    id
    @18
    @1
    ax-resscn
    a1i
    fssd
    @2
    id
    3anim123i
    vx
    cA
    cF
    cG
    cV
    fdivmpt
    syl
    adantr
    @7
    cX
    wceq
    #
    @10
    @13
    wceq
    @6
    @19
    @8
    @11
    @9
    @12
    cdiv
    @7
    cX
    cF
    fveq2
    @7
    cX
    cG
    fveq2
    oveq12d
    adantl
    @3
    @5
    simpr
    @6
    @11
    @12
    cdiv
    ovexd
    fvmptd
end
