include "cxp.mm"
include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "ccnv.mm"
include "cuni.mm"
include "cmpt.mm"
include "wf1o.mm"
include "cen.mm"
include "wbr.mm"
include "xpex.mm"
include "eqid.mm"
include "xpcomf1o.mm"
include "f1oen2g.mm"
include "mp3an.mm"

theorem xpcomen
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume xpcomen.1: |- A e. _V
  assume xpcomen.2: |- B e. _V


  assert |- ( A X. B ) ~~ ( B X. A )

  proof
    cA
    cB
    cxp
    #
    cvv
    wcel
    cB
    cA
    cxp
    #
    cvv
    wcel
    @0
    @1
    vx
    @0
    vx
    cv
    csn
    ccnv
    cuni
    cmpt
    #
    wf1o
    @0
    @1
    cen
    wbr
    cA
    cB
    xpcomen.1
    xpcomen.2
    xpex
    cB
    cA
    xpcomen.2
    xpcomen.1
    xpex
    vx
    cA
    cB
    @2
    @2
    eqid
    xpcomf1o
    @0
    @1
    @2
    cvv
    cvv
    f1oen2g
    mp3an
end
