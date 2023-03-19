include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "csubg.mm"
include "c0g.mm"
include "wceq.mm"
include "subrgsubg.mm"
include "subg0.mm"
include "syl.mm"

theorem subrg0
  let cA: class A
  let cR: class R
  let cS: class S
  let c.0: class .0.
  assume subrg0.1: |- S = ( R |`s A )
  assume subrg0.2: |- .0. = ( 0g ` R )


  assert |- ( A e. ( SubRing ` R ) -> .0. = ( 0g ` S ) )

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
    c.0
    cS
    c0g
    cfv
    wceq
    cA
    cR
    subrgsubg
    cA
    cR
    cS
    c.0
    subrg0.1
    subrg0.2
    subg0
    syl
end
