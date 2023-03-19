include "crg.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "cvv.mm"
include "wb.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "hashen1.mm"
include "mp1i.mm"
include "wa.mm"
include "0ring01eq.mm"
include "eqcomd.mm"
include "ex.mm"
include "eqcom.mm"
include "csn.mm"
include "01eq0ring.mm"
include "fveq2.mm"
include "c0g.mm"
include "hashsng.mm"
include "eqtrd.mm"
include "syl.mm"
include "syl5bi.mm"
include "impbid.mm"
include "bitr3d.mm"

theorem 0ring01eqbi
  let cB: class B
  let cR: class R
  let c.1: class .1.
  let c.0: class .0.
  assume 0ring.b: |- B = ( Base ` R )
  assume 0ring.0: |- .0. = ( 0g ` R )
  assume 0ring01eq.1: |- .1. = ( 1r ` R )


  assert |- ( R e. Ring -> ( B ~~ 1o <-> .1. = .0. ) )

  proof
    cR
    crg
    wcel
    #
    cB
    chash
    cfv
    #
    c1
    wceq
    #
    cB
    c1o
    cen
    wbr
    #
    c.1
    c.0
    wceq
    #
    cB
    cvv
    wcel
    @2
    @3
    wb
    @0
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
    mp1i
    @0
    @2
    @4
    @0
    @2
    @4
    @0
    @2
    wa
    c.0
    c.1
    cB
    cR
    c.1
    c.0
    0ring.b
    0ring.0
    0ring01eq.1
    0ring01eq
    eqcomd
    ex
    @4
    c.0
    c.1
    wceq
    #
    @0
    @2
    c.1
    c.0
    eqcom
    @0
    @5
    @2
    @0
    @5
    wa
    cB
    c.0
    csn
    #
    wceq
    #
    @2
    cB
    cR
    c.1
    c.0
    0ring.b
    0ring.0
    0ring01eq.1
    01eq0ring
    @7
    @1
    @6
    chash
    cfv
    #
    c1
    cB
    @6
    chash
    fveq2
    c.0
    cvv
    wcel
    @8
    c1
    wceq
    @7
    c.0
    cR
    c0g
    cfv
    cvv
    0ring.0
    cR
    c0g
    fvex
    eqeltri
    c.0
    cvv
    hashsng
    mp1i
    eqtrd
    syl
    ex
    syl5bi
    impbid
    bitr3d
end
