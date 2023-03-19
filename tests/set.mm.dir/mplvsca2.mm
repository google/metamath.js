include "cvsca.mm"
include "cfv.mm"
include "cbs.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "eqid.mm"
include "mplval2.mm"
include "ressvsca.mm"
include "ax-mp.mm"
include "eqtr4i.mm"

theorem mplvsca2
  let cP: class P
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cI: class I
  assume mplvsca2.p: |- P = ( I mPoly R )
  assume mplvsca2.s: |- S = ( I mPwSer R )
  assume mplvsca2.n: |- .x. = ( .s ` P )


  assert |- .x. = ( .s ` S )

  proof
    c.x
    cP
    cvsca
    cfv
    #
    cS
    cvsca
    cfv
    #
    mplvsca2.n
    cP
    cbs
    cfv
    #
    cvv
    wcel
    @1
    @0
    wceq
    cP
    cbs
    fvex
    @2
    @1
    cS
    cP
    cvv
    cP
    cR
    cS
    @2
    cI
    mplvsca2.p
    mplvsca2.s
    @2
    eqid
    mplval2
    @1
    eqid
    ressvsca
    ax-mp
    eqtr4i
end
