include "c0.mm"
include "cen.mm"
include "wbr.mm"
include "wceq.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "bren.mm"
include "ccnv.mm"
include "f1ocnv.mm"
include "f1o00.mm"
include "simprbi.mm"
include "syl.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "0ex.mm"
include "enref.mm"
include "breq1.mm"
include "mpbiri.mm"
include "impbii.mm"

theorem en0
  let cA: class A
  let vf: setvar f


  assert |- ( A ~~ (/) <-> A = (/) )

  proof
    cA
    c0
    cen
    wbr
    #
    cA
    c0
    wceq
    #
    @0
    cA
    c0
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    @1
    cA
    c0
    vf
    bren
    @3
    @1
    vf
    @3
    c0
    cA
    @2
    ccnv
    #
    wf1o
    #
    @1
    cA
    c0
    @2
    f1ocnv
    @5
    @4
    c0
    wceq
    @1
    cA
    @4
    f1o00
    simprbi
    syl
    exlimiv
    sylbi
    @1
    @0
    c0
    c0
    cen
    wbr
    c0
    0ex
    enref
    cA
    c0
    c0
    cen
    breq1
    mpbiri
    impbii
end
