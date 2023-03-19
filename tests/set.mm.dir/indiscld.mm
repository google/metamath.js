include "c0.mm"
include "cpr.mm"
include "ccld.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "cid.mm"
include "wss.mm"
include "cdif.mm"
include "wa.mm"
include "ctop.mm"
include "wb.mm"
include "indistop.mm"
include "indisuni.mm"
include "iscld.mm"
include "ax-mp.mm"
include "wceq.mm"
include "simpl.mm"
include "dfss4.mm"
include "sylib.mm"
include "wo.mm"
include "simpr.mm"
include "indislem.mm"
include "syl6eleqr.mm"
include "elpri.mm"
include "difeq2.mm"
include "dif0.mm"
include "syl6eq.mm"
include "fvex.mm"
include "prid2.mm"
include "eleqtri.mm"
include "syl6eqel.mm"
include "difid.mm"
include "0ex.mm"
include "prid1.mm"
include "jaoi.mm"
include "3syl.mm"
include "eqeltrrd.mm"
include "sylbi.mm"
include "ssriv.mm"
include "0cld.mm"
include "topcld.mm"
include "prssi.mm"
include "mp2an.mm"
include "eqsstr3i.mm"
include "eqssi.mm"

theorem indiscld
  let cA: class A
  let vx: setvar x
  let cV: class V


  assert |- ( Clsd ` { (/) , A } ) = { (/) , A }

  proof
    c0
    cA
    cpr
    #
    ccld
    cfv
    #
    @0
    vx
    @1
    @0
    vx
    cv
    #
    @1
    wcel
    #
    @2
    cA
    cid
    cfv
    #
    wss
    #
    @4
    @2
    cdif
    #
    @0
    wcel
    #
    wa
    #
    @2
    @0
    wcel
    @0
    ctop
    wcel
    #
    @3
    @8
    wb
    cA
    indistop
    #
    @2
    @0
    @4
    cA
    indisuni
    #
    iscld
    ax-mp
    @8
    @4
    @6
    cdif
    #
    @2
    @0
    @8
    @5
    @12
    @2
    wceq
    @5
    @7
    simpl
    @2
    @4
    dfss4
    sylib
    @8
    @6
    c0
    @4
    cpr
    #
    wcel
    @6
    c0
    wceq
    #
    @6
    @4
    wceq
    #
    wo
    @12
    @0
    wcel
    #
    @8
    @6
    @0
    @13
    @5
    @7
    simpr
    cA
    indislem
    #
    syl6eleqr
    @6
    c0
    @4
    elpri
    @14
    @16
    @15
    @14
    @12
    @4
    @0
    @14
    @12
    @4
    c0
    cdif
    @4
    @6
    c0
    @4
    difeq2
    @4
    dif0
    syl6eq
    @4
    @13
    @0
    c0
    @4
    cA
    cid
    fvex
    prid2
    @17
    eleqtri
    syl6eqel
    @15
    @12
    c0
    @0
    @15
    @12
    @4
    @4
    cdif
    c0
    @6
    @4
    @4
    difeq2
    @4
    difid
    syl6eq
    c0
    cA
    0ex
    prid1
    syl6eqel
    jaoi
    3syl
    eqeltrrd
    sylbi
    ssriv
    @0
    @13
    @1
    @17
    c0
    @1
    wcel
    #
    @4
    @1
    wcel
    #
    @13
    @1
    wss
    @9
    @18
    @10
    @0
    0cld
    ax-mp
    @9
    @19
    @10
    @0
    @4
    @11
    topcld
    ax-mp
    c0
    @4
    @1
    prssi
    mp2an
    eqsstr3i
    eqssi
end
