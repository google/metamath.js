include "wcel.mm"
include "cassintop.mm"
include "cfv.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "cmap.mm"
include "casslaw.mm"
include "wbr.mm"
include "crab.mm"
include "assintopmap.mm"
include "eleq2d.mm"
include "breq1.mm"
include "elrab.mm"
include "syl6bb.mm"
include "elmapi.mm"
include "ad2antrl.mm"
include "isasslaw.mm"
include "biimpd.mm"
include "impancom.mm"
include "impcom.mm"
include "jca.mm"
include "ex.mm"
include "sylbid.mm"
include "cclintop.mm"
include "wi.mm"
include "isclintop.mm"
include "biimprcd.mm"
include "adantr.mm"
include "cvv.mm"
include "wb.mm"
include "sqxpexg.mm"
include "fex.mm"
include "sylan2.mm"
include "ancoms.mm"
include "simpl.mm"
include "bicomd.mm"
include "syl2anc.mm"
include "impr.mm"
include "assintopval.mm"
include "mpbir2and.mm"
include "impbid.mm"

theorem isassintop
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cM: class M
  let cV: class V
  let c.op: class .o.
  let vo: setvar o
  let vk: setvar k

  disjoint M x
  disjoint M y
  disjoint M z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint .o. x
  disjoint .o. y
  disjoint .o. z
  disjoint M o
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint .o. o
  disjoint k x
  assert |- ( M e. V -> ( .o. e. ( assIntOp ` M ) <-> ( .o. : ( M X. M ) --> M /\ A. x e. M A. y e. M A. z e. M ( ( x .o. y ) .o. z ) = ( x .o. ( y .o. z ) ) ) ) )

  proof
    cM
    cV
    wcel
    #
    c.op
    cM
    cassintop
    cfv
    #
    wcel
    #
    cM
    cM
    cxp
    #
    cM
    c.op
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    c.op
    co
    vz
    cv
    #
    c.op
    co
    @5
    @6
    @7
    c.op
    co
    c.op
    co
    wceq
    vz
    cM
    wral
    vy
    cM
    wral
    vx
    cM
    wral
    #
    wa
    #
    @0
    @2
    c.op
    cM
    @3
    cmap
    co
    #
    wcel
    #
    c.op
    cM
    casslaw
    wbr
    #
    wa
    #
    @9
    @0
    @2
    c.op
    vo
    cv
    #
    cM
    casslaw
    wbr
    #
    vo
    @10
    crab
    #
    wcel
    @13
    @0
    @1
    @16
    c.op
    vo
    cM
    cV
    assintopmap
    eleq2d
    @15
    @12
    vo
    c.op
    @10
    @14
    c.op
    cM
    casslaw
    breq1
    #
    elrab
    syl6bb
    @0
    @13
    @9
    @0
    @13
    wa
    @4
    @8
    @11
    @4
    @0
    @12
    c.op
    cM
    @3
    elmapi
    ad2antrl
    @13
    @0
    @8
    @11
    @0
    @12
    @8
    @11
    @0
    wa
    @12
    @8
    vx
    vy
    vz
    cM
    @10
    cV
    c.op
    isasslaw
    biimpd
    impancom
    impcom
    jca
    ex
    sylbid
    @0
    @9
    @2
    @0
    @9
    wa
    #
    @2
    c.op
    cM
    cclintop
    cfv
    #
    wcel
    #
    @12
    @9
    @0
    @20
    @4
    @0
    @20
    wi
    @8
    @0
    @20
    @4
    cM
    cV
    c.op
    isclintop
    biimprcd
    adantr
    impcom
    @0
    @4
    @8
    @12
    @0
    @4
    wa
    #
    @8
    @12
    @21
    c.op
    cvv
    wcel
    #
    @0
    @8
    @12
    wb
    @4
    @0
    @22
    @0
    @4
    @3
    cvv
    wcel
    @22
    cM
    cV
    sqxpexg
    @3
    cM
    cvv
    c.op
    fex
    sylan2
    ancoms
    @0
    @4
    simpl
    @22
    @0
    wa
    @12
    @8
    vx
    vy
    vz
    cM
    cvv
    cV
    c.op
    isasslaw
    bicomd
    syl2anc
    biimpd
    impr
    @18
    @2
    c.op
    @15
    vo
    @19
    crab
    #
    wcel
    @20
    @12
    wa
    @18
    @1
    @23
    c.op
    @0
    @1
    @23
    wceq
    @9
    vo
    cM
    cV
    assintopval
    adantr
    eleq2d
    @15
    @12
    vo
    c.op
    @19
    @17
    elrab
    syl6bb
    mpbir2and
    ex
    impbid
end
