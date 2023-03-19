include "wss.mm"
include "wfun.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "csn.mm"
include "cima.mm"
include "wi.mm"
include "wa.mm"
include "cop.mm"
include "funfvop.mm"
include "ssel.mm"
include "syl5.mm"
include "imp.mm"
include "wb.mm"
include "cv.mm"
include "wceq.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "eleq2d.mm"
include "opeq1.mm"
include "eleq1d.mm"
include "vex.mm"
include "fvex.mm"
include "elimasn.mm"
include "vtoclbg.mm"
include "ad2antll.mm"
include "mpbird.mm"
include "exp32.mm"
include "impcom.mm"

theorem funfvima3
  let cA: class A
  let cF: class F
  let cG: class G
  let vx: setvar x


  assert |- ( ( Fun F /\ F C_ G ) -> ( A e. dom F -> ( F ` A ) e. ( G " { A } ) ) )

  proof
    cF
    cG
    wss
    #
    cF
    wfun
    #
    cA
    cF
    cdm
    #
    wcel
    #
    cA
    cF
    cfv
    #
    cG
    cA
    csn
    #
    cima
    #
    wcel
    #
    wi
    @0
    @1
    @3
    @7
    @0
    @1
    @3
    wa
    #
    wa
    @7
    cA
    @4
    cop
    #
    cG
    wcel
    #
    @0
    @8
    @10
    @8
    @9
    cF
    wcel
    @0
    @10
    cA
    cF
    funfvop
    cF
    cG
    @9
    ssel
    syl5
    imp
    @3
    @7
    @10
    wb
    @0
    @1
    @4
    cG
    vx
    cv
    #
    csn
    #
    cima
    #
    wcel
    @11
    @4
    cop
    #
    cG
    wcel
    @7
    @10
    vx
    cA
    @2
    @11
    cA
    wceq
    #
    @13
    @6
    @4
    @15
    @12
    @5
    cG
    @11
    cA
    sneq
    imaeq2d
    eleq2d
    @15
    @14
    @9
    cG
    @11
    cA
    @4
    opeq1
    eleq1d
    cG
    @11
    @4
    vx
    vex
    cA
    cF
    fvex
    elimasn
    vtoclbg
    ad2antll
    mpbird
    exp32
    impcom
end
