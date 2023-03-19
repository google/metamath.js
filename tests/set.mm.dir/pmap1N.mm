include "cops.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "crab.mm"
include "cbs.mm"
include "wceq.mm"
include "eqid.mm"
include "op1cl.mm"
include "pmapval.mm"
include "mpdan.mm"
include "wral.mm"
include "atbase.mm"
include "ople1.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "rabid2.mm"
include "sylibr.mm"
include "eqtr4d.mm"

theorem pmap1N
  let cA: class A
  let c.1: class .1.
  let cK: class K
  let cM: class M
  let vp: setvar p
  assume pmap1.u: |- .1. = ( 1. ` K )
  assume pmap1.a: |- A = ( Atoms ` K )
  assume pmap1.m: |- M = ( pmap ` K )


  assert |- ( K e. OP -> ( M ` .1. ) = A )

  proof
    cK
    cops
    wcel
    #
    c.1
    cM
    cfv
    #
    vp
    cv
    #
    c.1
    cK
    cple
    cfv
    #
    wbr
    #
    vp
    cA
    crab
    #
    cA
    @0
    c.1
    cK
    cbs
    cfv
    #
    wcel
    @1
    @5
    wceq
    @6
    c.1
    cK
    @6
    eqid
    #
    pmap1.u
    op1cl
    cA
    @6
    cops
    cK
    @3
    cM
    c.1
    vp
    @7
    @3
    eqid
    #
    pmap1.a
    pmap1.m
    pmapval
    mpdan
    @0
    @4
    vp
    cA
    wral
    cA
    @5
    wceq
    @0
    @4
    vp
    cA
    @2
    cA
    wcel
    @0
    @2
    @6
    wcel
    @4
    cA
    @6
    @2
    cK
    @7
    pmap1.a
    atbase
    @6
    c.1
    cK
    @3
    @2
    @7
    @8
    pmap1.u
    ople1
    sylan2
    ralrimiva
    @4
    vp
    cA
    rabid2
    sylibr
    eqtr4d
end
