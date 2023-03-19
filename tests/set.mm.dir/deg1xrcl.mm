include "cxr.mm"
include "deg1xrf.mm"
include "ffvelrni.mm"

theorem deg1xrcl
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cF: class F
  assume deg1xrf.d: |- D = ( deg1 ` R )
  assume deg1xrf.p: |- P = ( Poly1 ` R )
  assume deg1xrf.b: |- B = ( Base ` P )


  assert |- ( F e. B -> ( D ` F ) e. RR* )

  proof
    cB
    cxr
    cF
    cD
    cB
    cD
    cP
    cR
    deg1xrf.d
    deg1xrf.p
    deg1xrf.b
    deg1xrf
    ffvelrni
end
