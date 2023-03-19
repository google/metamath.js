include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "csubg.mm"
include "co.mm"
include "subrgsubg.mm"
include "subgcl.mm"
include "syl3an1.mm"

theorem subrgacl
  let cA: class A
  let c.pl: class .+
  let cR: class R
  let cX: class X
  let cY: class Y
  assume subrgacl.p: |- .+ = ( +g ` R )


  assert |- ( ( A e. ( SubRing ` R ) /\ X e. A /\ Y e. A ) -> ( X .+ Y ) e. A )

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
    cX
    cA
    wcel
    cY
    cA
    wcel
    cX
    cY
    c.pl
    co
    cA
    wcel
    cA
    cR
    subrgsubg
    c.pl
    cA
    cR
    cX
    cY
    subrgacl.p
    subgcl
    syl3an1
end
