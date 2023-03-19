include "crg.mm"
include "wcel.mm"
include "wceq.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "csn.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "w3o.mm"
include "wne.mm"
include "wi.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "hashv01gt1.mm"
include "ax-mp.mm"
include "c0.mm"
include "wb.mm"
include "hasheq0.mm"
include "ne0i.mm"
include "eqneqall.mm"
include "syl5com.mm"
include "syl5bi.mm"
include "ring0cl.mm"
include "syl11.mm"
include "a1d.mm"
include "wa.mm"
include "ring1ne0.mm"
include "necomd.mm"
include "ex.mm"
include "a1i.mm"
include "com13.mm"
include "3jaoi.mm"
include "necon4d.mm"
include "imp.mm"
include "0ring.mm"
include "syldan.mm"

theorem 01eq0ring
  let cB: class B
  let cR: class R
  let c.1: class .1.
  let c.0: class .0.
  assume 0ring.b: |- B = ( Base ` R )
  assume 0ring.0: |- .0. = ( 0g ` R )
  assume 0ring01eq.1: |- .1. = ( 1r ` R )


  assert |- ( ( R e. Ring /\ .0. = .1. ) -> B = { .0. } )

  proof
    cR
    crg
    wcel
    #
    c.0
    c.1
    wceq
    #
    cB
    chash
    cfv
    #
    c1
    wceq
    #
    cB
    c.0
    csn
    wceq
    @0
    @1
    @3
    @0
    @2
    c1
    c.0
    c.1
    @2
    cc0
    wceq
    #
    @3
    c1
    @2
    clt
    wbr
    #
    w3o
    #
    @0
    @2
    c1
    wne
    #
    c.0
    c.1
    wne
    #
    wi
    #
    wi
    #
    cB
    cvv
    wcel
    #
    @6
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
    #
    cB
    cvv
    hashv01gt1
    ax-mp
    @4
    @10
    @3
    @5
    c.0
    cB
    wcel
    #
    @4
    @9
    @0
    @4
    cB
    c0
    wceq
    #
    @13
    @9
    @11
    @4
    @14
    wb
    @12
    cB
    cvv
    hasheq0
    ax-mp
    @13
    cB
    c0
    wne
    @14
    @9
    cB
    c.0
    ne0i
    @9
    cB
    c0
    eqneqall
    syl5com
    syl5bi
    cB
    cR
    c.0
    0ring.b
    0ring.0
    ring0cl
    syl11
    @3
    @9
    @0
    @8
    @2
    c1
    eqneqall
    a1d
    @7
    @0
    @5
    @8
    @0
    @5
    @8
    wi
    wi
    @7
    @0
    @5
    @8
    @0
    @5
    wa
    c.1
    c.0
    cB
    cR
    c.1
    c.0
    0ring.b
    0ring01eq.1
    0ring.0
    ring1ne0
    necomd
    ex
    a1i
    com13
    3jaoi
    ax-mp
    necon4d
    imp
    cB
    cR
    c.0
    0ring.b
    0ring.0
    0ring
    syldan
end
