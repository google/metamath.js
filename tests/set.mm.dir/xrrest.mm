include "cr.mm"
include "wss.mm"
include "crest.mm"
include "co.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "cle.mm"
include "cordt.mm"
include "oveq1i.mm"
include "xrtgioo.mm"
include "eqtri.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "eqeltri.mm"
include "reex.mm"
include "restabs.mm"
include "mp3an13.mm"
include "syl5req.mm"

theorem xrrest
  let cA: class A
  let cR: class R
  let cX: class X
  assume xrrest.1: |- X = ( ordTop ` <_ )
  assume xrrest.2: |- R = ( topGen ` ran (,) )


  assert |- ( A C_ RR -> ( X |`t A ) = ( R |`t A ) )

  proof
    cA
    cr
    wss
    #
    cR
    cA
    crest
    co
    cX
    cr
    crest
    co
    #
    cA
    crest
    co
    #
    cX
    cA
    crest
    co
    #
    cR
    @1
    cA
    crest
    cR
    cioo
    crn
    ctg
    cfv
    @1
    xrrest.2
    @1
    cX
    cle
    cordt
    cfv
    #
    cr
    crest
    xrrest.1
    oveq1i
    xrtgioo
    eqtri
    oveq1i
    cX
    cvv
    wcel
    @0
    cr
    cvv
    wcel
    @2
    @3
    wceq
    cX
    @4
    cvv
    xrrest.1
    cle
    cordt
    fvex
    eqeltri
    reex
    cA
    cr
    cX
    cvv
    cvv
    restabs
    mp3an13
    syl5req
end
