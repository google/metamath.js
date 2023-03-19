include "wcel.mm"
include "wa.mm"
include "wf1o.mm"
include "wf.mm"
include "laut1o.mm"
include "f1of.mm"
include "syl.mm"
include "ffvelrnda.mm"

theorem lautcl
  let cB: class B
  let cF: class F
  let cI: class I
  let cK: class K
  let cV: class V
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume laut1o.b: |- B = ( Base ` K )
  assume laut1o.i: |- I = ( LAut ` K )


  assert |- ( ( ( K e. V /\ F e. I ) /\ X e. B ) -> ( F ` X ) e. B )

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
    cX
    cF
    @0
    cB
    cB
    cF
    wf1o
    cB
    cB
    cF
    wf
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
    f1of
    syl
    ffvelrnda
end
