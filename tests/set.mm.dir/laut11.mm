include "wcel.mm"
include "wa.mm"
include "wf1.mm"
include "cfv.mm"
include "wceq.mm"
include "wb.mm"
include "wf1o.mm"
include "laut1o.mm"
include "f1of1.mm"
include "syl.mm"
include "f1fveq.mm"
include "sylan.mm"

theorem laut11
  let cB: class B
  let cF: class F
  let cI: class I
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume laut1o.b: |- B = ( Base ` K )
  assume laut1o.i: |- I = ( LAut ` K )


  assert |- ( ( ( K e. V /\ F e. I ) /\ ( X e. B /\ Y e. B ) ) -> ( ( F ` X ) = ( F ` Y ) <-> X = Y ) )

  proof
    cK
    cV
    wcel
    cF
    cI
    wcel
    wa
    #
    cB
    cB
    cF
    wf1
    #
    cX
    cB
    wcel
    cY
    cB
    wcel
    wa
    cX
    cF
    cfv
    cY
    cF
    cfv
    wceq
    cX
    cY
    wceq
    wb
    @0
    cB
    cB
    cF
    wf1o
    @1
    cV
    cB
    cF
    cI
    cK
    laut1o.b
    laut1o.i
    laut1o
    cB
    cB
    cF
    f1of1
    syl
    cB
    cB
    cX
    cY
    cF
    f1fveq
    sylan
end
