include "c1o.mm"
include "con0.mm"
include "wcel.mm"
include "crg.mm"
include "cfv.mm"
include "cmnf.mm"
include "wceq.mm"
include "1on.mm"
include "cmpl.mm"
include "co.mm"
include "deg1fval.mm"
include "eqid.mm"
include "ply1mpl0.mm"
include "mdeg0.mm"
include "mpan.mm"

theorem deg1z
  let cD: class D
  let cP: class P
  let cR: class R
  let c.0: class .0.
  assume deg1z.d: |- D = ( deg1 ` R )
  assume deg1z.p: |- P = ( Poly1 ` R )
  assume deg1z.z: |- .0. = ( 0g ` P )


  assert |- ( R e. Ring -> ( D ` .0. ) = -oo )

  proof
    c1o
    con0
    wcel
    cR
    crg
    wcel
    c.0
    cD
    cfv
    cmnf
    wceq
    1on
    cD
    c1o
    cR
    cmpl
    co
    #
    cR
    c1o
    con0
    c.0
    cD
    cR
    deg1z.d
    deg1fval
    @0
    eqid
    #
    cP
    cR
    @0
    c.0
    @1
    deg1z.p
    deg1z.z
    ply1mpl0
    mdeg0
    mpan
end
