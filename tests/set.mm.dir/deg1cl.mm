include "c1o.mm"
include "cmpl.mm"
include "co.mm"
include "deg1fval.mm"
include "eqid.mm"
include "cps1.mm"
include "cfv.mm"
include "ply1bas.mm"
include "mdegcl.mm"

theorem deg1cl
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cF: class F
  assume deg1xrf.d: |- D = ( deg1 ` R )
  assume deg1xrf.p: |- P = ( Poly1 ` R )
  assume deg1xrf.b: |- B = ( Base ` P )


  assert |- ( F e. B -> ( D ` F ) e. ( NN0 u. { -oo } ) )

  proof
    cB
    cD
    c1o
    cR
    cmpl
    co
    #
    cR
    cF
    c1o
    cD
    cR
    deg1xrf.d
    deg1fval
    @0
    eqid
    cP
    cR
    cR
    cps1
    cfv
    #
    cB
    deg1xrf.p
    @1
    eqid
    deg1xrf.b
    ply1bas
    mdegcl
end
