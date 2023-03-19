include "cr.mm"
include "wss.mm"
include "crest.mm"
include "co.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "eqid.mm"
include "rerest.mm"
include "xrrest.mm"
include "eqtr4d.mm"

theorem xrrest2
  let cA: class A
  let cJ: class J
  let cX: class X
  assume xrrest2.1: |- J = ( TopOpen ` CCfld )
  assume xrrest2.2: |- X = ( ordTop ` <_ )


  assert |- ( A C_ RR -> ( J |`t A ) = ( X |`t A ) )

  proof
    cA
    cr
    wss
    cJ
    cA
    crest
    co
    cioo
    crn
    ctg
    cfv
    #
    cA
    crest
    co
    cX
    cA
    crest
    co
    cA
    @0
    cJ
    xrrest2.1
    @0
    eqid
    #
    rerest
    cA
    @0
    cX
    xrrest2.2
    @1
    xrrest
    eqtr4d
end
