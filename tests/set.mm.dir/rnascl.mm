include "casa.mm"
include "wcel.mm"
include "csn.mm"
include "cfv.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "wceq.mm"
include "csca.mm"
include "cbs.mm"
include "wrex.mm"
include "cab.mm"
include "crn.mm"
include "clmod.mm"
include "assalmod.mm"
include "crg.mm"
include "assaring.mm"
include "eqid.mm"
include "ringidcl.mm"
include "syl.mm"
include "lspsn.mm"
include "syl2anc.mm"
include "asclfval.mm"
include "rnmpt.mm"
include "syl6reqr.mm"

theorem rnascl
  let cA: class A
  let c.1: class .1.
  let cN: class N
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume rnascl.a: |- A = ( algSc ` W )
  assume rnascl.o: |- .1. = ( 1r ` W )
  assume rnascl.n: |- N = ( LSpan ` W )


  assert |- ( W e. AssAlg -> ran A = ( N ` { .1. } ) )

  proof
    cW
    casa
    wcel
    #
    c.1
    csn
    cN
    cfv
    #
    vx
    cv
    vy
    cv
    c.1
    cW
    cvsca
    cfv
    #
    co
    #
    wceq
    vy
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    wrex
    vx
    cab
    #
    cA
    crn
    @0
    cW
    clmod
    wcel
    c.1
    cW
    cbs
    cfv
    #
    wcel
    #
    @1
    @6
    wceq
    cW
    assalmod
    @0
    cW
    crg
    wcel
    @8
    cW
    assaring
    @7
    cW
    c.1
    @7
    eqid
    #
    rnascl.o
    ringidcl
    syl
    vx
    @2
    vy
    @4
    @5
    cN
    @7
    cW
    c.1
    @4
    eqid
    #
    @5
    eqid
    #
    @9
    @2
    eqid
    #
    rnascl.n
    lspsn
    syl2anc
    vy
    vx
    @5
    @3
    cA
    vy
    cA
    @2
    c.1
    @4
    @5
    cW
    rnascl.a
    @10
    @11
    @12
    rnascl.o
    asclfval
    rnmpt
    syl6reqr
end
