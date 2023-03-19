include "crg.mm"
include "wcel.mm"
include "csn.mm"
include "cfv.mm"
include "wceq.mm"
include "wss.mm"
include "ringidcl.mm"
include "snssd.mm"
include "rspssid.mm"
include "mpdan.mm"
include "cur.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "snss.mm"
include "sylibr.mm"
include "clidl.mm"
include "wb.mm"
include "eqid.mm"
include "rspcl.mm"
include "lidl1el.mm"
include "mpbid.mm"

theorem rsp1
  let cB: class B
  let cR: class R
  let c.1: class .1.
  let cK: class K
  assume rspcl.k: |- K = ( RSpan ` R )
  assume rspcl.b: |- B = ( Base ` R )
  assume rsp1.o: |- .1. = ( 1r ` R )


  assert |- ( R e. Ring -> ( K ` { .1. } ) = B )

  proof
    cR
    crg
    wcel
    #
    c.1
    c.1
    csn
    #
    cK
    cfv
    #
    wcel
    #
    @2
    cB
    wceq
    #
    @0
    @1
    @2
    wss
    #
    @3
    @0
    @1
    cB
    wss
    #
    @5
    @0
    c.1
    cB
    cB
    cR
    c.1
    rspcl.b
    rsp1.o
    ringidcl
    snssd
    #
    cB
    cR
    @1
    cK
    rspcl.k
    rspcl.b
    rspssid
    mpdan
    c.1
    @2
    c.1
    cR
    cur
    cfv
    cvv
    rsp1.o
    cR
    cur
    fvex
    eqeltri
    snss
    sylibr
    @0
    @2
    cR
    clidl
    cfv
    #
    wcel
    #
    @3
    @4
    wb
    @0
    @6
    @9
    @7
    cB
    cR
    @8
    @1
    cK
    rspcl.k
    rspcl.b
    @8
    eqid
    #
    rspcl
    mpdan
    cB
    cR
    @8
    c.1
    @2
    @10
    rspcl.b
    rsp1.o
    lidl1el
    mpdan
    mpbid
end
