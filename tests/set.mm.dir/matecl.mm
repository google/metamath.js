include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "w3a.mm"
include "cfn.mm"
include "cvv.mm"
include "wa.mm"
include "co.mm"
include "eqid.mm"
include "matrcl.mm"
include "3ad2ant3.mm"
include "wi.mm"
include "cxp.mm"
include "cmap.mm"
include "matbas2.mm"
include "eqcomd.mm"
include "eleq2d.mm"
include "wf.mm"
include "wb.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "sqxpexg.mm"
include "elmapg.mm"
include "syl2anr.mm"
include "wfn.mm"
include "cv.mm"
include "wral.mm"
include "ffnov.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "com12.mm"
include "adantl.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "com13.mm"
include "ex.mm"
include "3imp1.mm"
include "mpdan.mm"

theorem matecl
  let cA: class A
  let cR: class R
  let cI: class I
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  assume matecl.a: |- A = ( N Mat R )
  assume matecl.k: |- K = ( Base ` R )


  assert |- ( ( I e. N /\ J e. N /\ M e. ( Base ` A ) ) -> ( I M J ) e. K )

  proof
    cI
    cN
    wcel
    #
    cJ
    cN
    wcel
    #
    cM
    cA
    cbs
    cfv
    #
    wcel
    #
    w3a
    cN
    cfn
    wcel
    #
    cR
    cvv
    wcel
    #
    wa
    #
    cI
    cJ
    cM
    co
    #
    cK
    wcel
    #
    @3
    @0
    @6
    @1
    cA
    @2
    cR
    cN
    cM
    matecl.a
    @2
    eqid
    matrcl
    3ad2ant3
    @0
    @1
    @3
    @6
    @8
    @0
    @1
    @3
    @6
    @8
    wi
    wi
    @6
    @3
    @0
    @1
    wa
    #
    @8
    @6
    @3
    cM
    cK
    cN
    cN
    cxp
    #
    cmap
    co
    #
    wcel
    #
    @9
    @8
    wi
    #
    @6
    @2
    @11
    cM
    @6
    @11
    @2
    cA
    cR
    cK
    cN
    cvv
    matecl.a
    matecl.k
    matbas2
    eqcomd
    eleq2d
    @6
    @12
    @10
    cK
    cM
    wf
    #
    @13
    @5
    cK
    cvv
    wcel
    #
    @10
    cvv
    wcel
    @12
    @14
    wb
    @4
    @15
    @5
    cK
    cR
    cbs
    cfv
    cvv
    matecl.k
    cR
    cbs
    fvex
    eqeltri
    a1i
    cN
    cfn
    sqxpexg
    cK
    @10
    cM
    cvv
    cvv
    elmapg
    syl2anr
    @14
    cM
    @10
    wfn
    #
    vi
    cv
    #
    vj
    cv
    #
    cM
    co
    #
    cK
    wcel
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    wa
    #
    @6
    @13
    vi
    vj
    cN
    cN
    cK
    cM
    ffnov
    @22
    @13
    wi
    @6
    @21
    @13
    @16
    @9
    @21
    @8
    @20
    @8
    cI
    @18
    cM
    co
    #
    cK
    wcel
    vi
    vj
    cI
    cJ
    cN
    cN
    @17
    cI
    wceq
    @19
    @23
    cK
    @17
    cI
    @18
    cM
    oveq1
    eleq1d
    @18
    cJ
    wceq
    @23
    @7
    cK
    @18
    cJ
    cI
    cM
    oveq2
    eleq1d
    rspc2v
    com12
    adantl
    a1i
    syl5bi
    sylbid
    sylbid
    com13
    ex
    3imp1
    mpdan
end
