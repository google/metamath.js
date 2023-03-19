include "wfn.mm"
include "wss.mm"
include "wa.mm"
include "cima.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "cvv.mm"
include "elex.mm"
include "anim2i.mm"
include "fvex.mm"
include "eleq1.mm"
include "mpbii.mm"
include "rexlimivw.mm"
include "wb.mm"
include "wi.mm"
include "eqeq2.mm"
include "rexbidv.mm"
include "bibi12d.mm"
include "imbi2d.mm"
include "wfun.mm"
include "cdm.mm"
include "cab.mm"
include "fnfun.mm"
include "fndm.mm"
include "sseq2d.mm"
include "biimpar.mm"
include "dfimafn.mm"
include "syl2an2r.mm"
include "abeq2d.mm"
include "vtoclg.mm"
include "impcom.mm"
include "pm5.21nd.mm"

theorem fvelimab
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vy: setvar y

  disjoint B x
  disjoint C x
  disjoint F x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint C y
  disjoint F y
  assert |- ( ( F Fn A /\ B C_ A ) -> ( C e. ( F " B ) <-> E. x e. B ( F ` x ) = C ) )

  proof
    cF
    cA
    wfn
    #
    cB
    cA
    wss
    #
    wa
    #
    cC
    cF
    cB
    cima
    #
    wcel
    #
    vx
    cv
    #
    cF
    cfv
    #
    cC
    wceq
    #
    vx
    cB
    wrex
    #
    @2
    cC
    cvv
    wcel
    #
    wa
    @4
    @9
    @2
    cC
    @3
    elex
    anim2i
    @8
    @9
    @2
    @7
    @9
    vx
    cB
    @7
    @6
    cvv
    wcel
    @9
    @5
    cF
    fvex
    @6
    cC
    cvv
    eleq1
    mpbii
    rexlimivw
    anim2i
    @9
    @2
    @4
    @8
    wb
    #
    @2
    vy
    cv
    #
    @3
    wcel
    #
    @6
    @11
    wceq
    #
    vx
    cB
    wrex
    #
    wb
    #
    wi
    @2
    @10
    wi
    vy
    cC
    cvv
    @11
    cC
    wceq
    #
    @15
    @10
    @2
    @16
    @12
    @4
    @14
    @8
    @11
    cC
    @3
    eleq1
    @16
    @13
    @7
    vx
    cB
    @11
    cC
    @6
    eqeq2
    rexbidv
    bibi12d
    imbi2d
    @2
    @14
    vy
    @3
    @0
    cF
    wfun
    @1
    cB
    cF
    cdm
    #
    wss
    #
    @3
    @14
    vy
    cab
    wceq
    cA
    cF
    fnfun
    @0
    @18
    @1
    @0
    @17
    cA
    cB
    cA
    cF
    fndm
    sseq2d
    biimpar
    vx
    vy
    cB
    cF
    dfimafn
    syl2an2r
    abeq2d
    vtoclg
    impcom
    pm5.21nd
end
