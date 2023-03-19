include "cnq.mm"
include "wcel.mm"
include "cv.mm"
include "cplq.mm"
include "co.mm"
include "wceq.mm"
include "wex.mm"
include "cltq.mm"
include "wbr.mm"
include "halfnq.mm"
include "eleq1a.mm"
include "wa.mm"
include "cxp.mm"
include "addnqf.mm"
include "fdmi.mm"
include "0nnq.mm"
include "ndmovrcl.mm"
include "ltaddnq.mm"
include "syl.mm"
include "syl6.mm"
include "breq2.mm"
include "mpbidi.mm"
include "eximdv.mm"
include "mpd.mm"

theorem nsmallnq
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. Q. -> E. x x <Q A )

  proof
    cA
    cnq
    wcel
    #
    vx
    cv
    #
    @1
    cplq
    co
    #
    cA
    wceq
    #
    vx
    wex
    @1
    cA
    cltq
    wbr
    #
    vx
    wex
    vx
    cA
    halfnq
    @0
    @3
    @4
    vx
    @3
    @1
    @2
    cltq
    wbr
    #
    @4
    @0
    @0
    @3
    @2
    cnq
    wcel
    #
    @5
    cA
    cnq
    @2
    eleq1a
    @6
    @1
    cnq
    wcel
    #
    @7
    wa
    @5
    @1
    @1
    cnq
    cplq
    cnq
    cnq
    cxp
    cnq
    cplq
    addnqf
    fdmi
    0nnq
    ndmovrcl
    @1
    @1
    ltaddnq
    syl
    syl6
    @2
    cA
    @1
    cltq
    breq2
    mpbidi
    eximdv
    mpd
end
