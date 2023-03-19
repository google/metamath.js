include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "csubg.mm"
include "cbs.mm"
include "wceq.mm"
include "subrgsubg.mm"
include "subgbas.mm"
include "syl.mm"

theorem subrgbas
  let cA: class A
  let cR: class R
  let cS: class S
  assume subrgbas.b: |- S = ( R |`s A )


  assert |- ( A e. ( SubRing ` R ) -> A = ( Base ` S ) )

  proof
    cA
    cR
    csubrg
    cfv
    wcel
    cA
    cR
    csubg
    cfv
    wcel
    cA
    cS
    cbs
    cfv
    wceq
    cA
    cR
    subrgsubg
    cA
    cR
    cS
    subrgbas.b
    subgbas
    syl
end
