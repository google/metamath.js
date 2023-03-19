include "crg.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "csn.mm"
include "wi.mm"
include "ring0cl.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "cvv.mm"
include "wb.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "hashen1.mm"
include "ax-mp.mm"
include "en1eqsn.mm"
include "ex.mm"
include "syl5bi.mm"
include "syl.mm"
include "imp.mm"

theorem 0ring
  let cB: class B
  let cR: class R
  let c.0: class .0.
  assume 0ring.b: |- B = ( Base ` R )
  assume 0ring.0: |- .0. = ( 0g ` R )


  assert |- ( ( R e. Ring /\ ( # ` B ) = 1 ) -> B = { .0. } )

  proof
    cR
    crg
    wcel
    #
    cB
    chash
    cfv
    c1
    wceq
    #
    cB
    c.0
    csn
    wceq
    #
    @0
    c.0
    cB
    wcel
    #
    @1
    @2
    wi
    cB
    cR
    c.0
    0ring.b
    0ring.0
    ring0cl
    @1
    cB
    c1o
    cen
    wbr
    #
    @3
    @2
    cB
    cvv
    wcel
    @1
    @4
    wb
    cB
    cR
    cbs
    cfv
    cvv
    0ring.b
    cR
    cbs
    fvex
    eqeltri
    cB
    cvv
    hashen1
    ax-mp
    @3
    @4
    @2
    c.0
    cB
    en1eqsn
    ex
    syl5bi
    syl
    imp
end
