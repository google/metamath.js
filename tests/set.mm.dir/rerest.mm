include "cr.mm"
include "wss.mm"
include "crest.mm"
include "co.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "tgioo2.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "ctop.mm"
include "wcel.mm"
include "cvv.mm"
include "wceq.mm"
include "cnfldtop.mm"
include "reex.mm"
include "restabs.mm"
include "mp3an13.mm"
include "syl5req.mm"

theorem rerest
  let cA: class A
  let cR: class R
  let cJ: class J
  assume tgioo2.1: |- J = ( TopOpen ` CCfld )
  assume rerest.2: |- R = ( topGen ` ran (,) )


  assert |- ( A C_ RR -> ( J |`t A ) = ( R |`t A ) )

  proof
    cA
    cr
    wss
    #
    cR
    cA
    crest
    co
    cJ
    cr
    crest
    co
    #
    cA
    crest
    co
    #
    cJ
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
    rerest.2
    cJ
    tgioo2.1
    tgioo2
    eqtri
    oveq1i
    cJ
    ctop
    wcel
    @0
    cr
    cvv
    wcel
    @2
    @3
    wceq
    cJ
    tgioo2.1
    cnfldtop
    reex
    cA
    cr
    cJ
    ctop
    cvv
    restabs
    mp3an13
    syl5req
end
