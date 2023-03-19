include "wcel.mm"
include "ctskm.mm"
include "cfv.mm"
include "cv.mm"
include "ctsk.mm"
include "crab.mm"
include "cint.mm"
include "wi.mm"
include "wral.mm"
include "tskmval.mm"
include "eleq2d.mm"
include "cvv.mm"
include "elex.mm"
include "a1i.mm"
include "tskmid.mm"
include "tskmcl.mm"
include "wceq.mm"
include "eleq2.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "ax-mp.mm"
include "syl5com.mm"
include "syl6.mm"
include "wb.mm"
include "elintrabg.mm"
include "pm5.21ndd.mm"
include "bitrd.mm"

theorem eltskm
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V

  disjoint A x
  disjoint B x
  assert |- ( A e. V -> ( B e. ( tarskiMap ` A ) <-> A. x e. Tarski ( A e. x -> B e. x ) ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cA
    ctskm
    cfv
    #
    wcel
    #
    cB
    cA
    vx
    cv
    #
    wcel
    #
    vx
    ctsk
    crab
    cint
    #
    wcel
    #
    @4
    cB
    @3
    wcel
    #
    wi
    #
    vx
    ctsk
    wral
    #
    @0
    @1
    @5
    cB
    vx
    cA
    cV
    tskmval
    eleq2d
    @0
    cB
    cvv
    wcel
    #
    @6
    @9
    @6
    @10
    wi
    @0
    cB
    @5
    elex
    a1i
    @0
    @9
    @2
    @10
    @0
    cA
    @1
    wcel
    #
    @9
    @2
    cA
    cV
    tskmid
    @1
    ctsk
    wcel
    @9
    @11
    @2
    wi
    #
    wi
    cA
    tskmcl
    @8
    @12
    vx
    @1
    ctsk
    @3
    @1
    wceq
    @4
    @11
    @7
    @2
    @3
    @1
    cA
    eleq2
    @3
    @1
    cB
    eleq2
    imbi12d
    rspcv
    ax-mp
    syl5com
    cB
    @1
    elex
    syl6
    @10
    @6
    @9
    wb
    wi
    @0
    @4
    vx
    cB
    ctsk
    cvv
    elintrabg
    a1i
    pm5.21ndd
    bitrd
end
