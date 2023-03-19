include "ccnv.mm"
include "cdif.mm"
include "cfv.mm"
include "c0.mm"
include "csn.mm"
include "wcel.mm"
include "wceq.mm"
include "crn.mm"
include "cun.mm"
include "fvrn0.mm"
include "wss.mm"
include "rnnonrel.mm"
include "0ss.mm"
include "eqsstri.mm"
include "ssequn1.mm"
include "mpbi.mm"
include "eleqtri.mm"
include "fvex.mm"
include "elsn.mm"

theorem fvnonrel
  let cA: class A
  let cX: class X


  assert |- ( ( A \ `' `' A ) ` X ) = (/)

  proof
    cX
    cA
    cA
    ccnv
    ccnv
    cdif
    #
    cfv
    #
    c0
    csn
    #
    wcel
    @1
    c0
    wceq
    @1
    @0
    crn
    #
    @2
    cun
    #
    @2
    @0
    cX
    fvrn0
    @3
    @2
    wss
    @4
    @2
    wceq
    @3
    c0
    @2
    cA
    rnnonrel
    @2
    0ss
    eqsstri
    @3
    @2
    ssequn1
    mpbi
    eleqtri
    @1
    c0
    cX
    @0
    fvex
    elsn
    mpbi
end
