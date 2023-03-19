include "chf.mm"
include "wcel.mm"
include "cr1.mm"
include "com.mm"
include "cima.mm"
include "cuni.mm"
include "cv.mm"
include "cfv.mm"
include "wrex.mm"
include "df-hf.mm"
include "eleq2i.mm"
include "con0.mm"
include "cvv.mm"
include "wf1.mm"
include "wfun.mm"
include "wb.mm"
include "r111.mm"
include "f1fun.mm"
include "eluniima.mm"
include "mp2b.mm"
include "bitri.mm"

theorem elhf
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. Hf <-> E. x e. _om A e. ( R1 ` x ) )

  proof
    cA
    chf
    wcel
    cA
    cr1
    com
    cima
    cuni
    #
    wcel
    #
    cA
    vx
    cv
    cr1
    cfv
    wcel
    vx
    com
    wrex
    #
    chf
    @0
    cA
    df-hf
    eleq2i
    con0
    cvv
    cr1
    wf1
    cr1
    wfun
    @1
    @2
    wb
    r111
    con0
    cvv
    cr1
    f1fun
    vx
    com
    cA
    cr1
    eluniima
    mp2b
    bitri
end
