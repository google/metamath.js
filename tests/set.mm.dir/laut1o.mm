include "wcel.mm"
include "wf1o.mm"
include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wb.mm"
include "wral.mm"
include "eqid.mm"
include "islaut.mm"
include "simprbda.mm"

theorem laut1o
  let cA: class A
  let cB: class B
  let cF: class F
  let cI: class I
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  assume laut1o.b: |- B = ( Base ` K )
  assume laut1o.i: |- I = ( LAut ` K )


  assert |- ( ( K e. A /\ F e. I ) -> F : B -1-1-onto-> B )

  proof
    cK
    cA
    wcel
    cF
    cI
    wcel
    cB
    cB
    cF
    wf1o
    vx
    cv
    #
    vy
    cv
    #
    cK
    cple
    cfv
    #
    wbr
    @0
    cF
    cfv
    @1
    cF
    cfv
    @2
    wbr
    wb
    vy
    cB
    wral
    vx
    cB
    wral
    vx
    vy
    cA
    cB
    cF
    cI
    cK
    @2
    laut1o.b
    @2
    eqid
    laut1o.i
    islaut
    simprbda
end
