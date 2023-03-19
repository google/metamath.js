include "csn.mm"
include "cxp.mm"
include "cucn.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "fconst6g.mm"
include "syl.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "cust.mm"
include "adantr.mm"
include "ustne0.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "ustref.mm"
include "syl3anc.mm"
include "wceq.mm"
include "simprl.mm"
include "fvconst2g.mm"
include "syl2anc.mm"
include "simprr.mm"
include "3brtr4d.mm"
include "a1d.mm"
include "ralrimivva.mm"
include "reximdva0.mm"
include "mpdan.mm"
include "ralrimiva.mm"
include "wb.mm"
include "isucn.mm"
include "mpbir2and.mm"

theorem cstucnd
  let wph: wff ph
  let cA: class A
  let cU: class U
  let cV: class V
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  assume cstucnd.1: |- ( ph -> U e. ( UnifOn ` X ) )
  assume cstucnd.2: |- ( ph -> V e. ( UnifOn ` Y ) )
  assume cstucnd.3: |- ( ph -> A e. Y )


  assert |- ( ph -> ( X X. { A } ) e. ( U uCn V ) )

  proof
    wph
    cX
    cA
    csn
    cxp
    #
    cU
    cV
    cucn
    co
    wcel
    #
    cX
    cY
    @0
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    vr
    cv
    #
    wbr
    #
    @3
    @0
    cfv
    #
    @4
    @0
    cfv
    #
    vs
    cv
    #
    wbr
    #
    wi
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    vr
    cU
    wrex
    #
    vs
    cV
    wral
    #
    wph
    cA
    cY
    wcel
    #
    @2
    cstucnd.3
    cX
    cA
    cY
    fconst6g
    syl
    wph
    @13
    vs
    cV
    wph
    @9
    cV
    wcel
    #
    wa
    #
    cU
    c0
    wne
    #
    @13
    @17
    cU
    cX
    cust
    cfv
    wcel
    #
    @18
    wph
    @19
    @16
    cstucnd.1
    adantr
    cU
    cX
    ustne0
    syl
    @17
    @12
    vr
    cU
    @17
    @5
    cU
    wcel
    #
    wa
    #
    @11
    vx
    vy
    cX
    cX
    @21
    @3
    cX
    wcel
    #
    @4
    cX
    wcel
    #
    wa
    #
    wa
    #
    @10
    @6
    @25
    cA
    cA
    @7
    @8
    @9
    @25
    cV
    cY
    cust
    cfv
    wcel
    #
    @16
    @15
    cA
    cA
    @9
    wbr
    wph
    @26
    @16
    @20
    @24
    cstucnd.2
    ad3antrrr
    wph
    @16
    @20
    @24
    simpllr
    wph
    @15
    @16
    @20
    @24
    cstucnd.3
    ad3antrrr
    #
    cA
    cV
    @9
    cY
    ustref
    syl3anc
    @25
    @15
    @22
    @7
    cA
    wceq
    @27
    @21
    @22
    @23
    simprl
    cX
    cA
    @3
    cY
    fvconst2g
    syl2anc
    @25
    @15
    @23
    @8
    cA
    wceq
    @27
    @21
    @22
    @23
    simprr
    cX
    cA
    @4
    cY
    fvconst2g
    syl2anc
    3brtr4d
    a1d
    ralrimivva
    reximdva0
    mpdan
    ralrimiva
    wph
    @19
    @26
    @1
    @2
    @14
    wa
    wb
    cstucnd.1
    cstucnd.2
    vx
    vy
    cU
    @0
    cV
    cX
    cY
    vs
    vr
    isucn
    syl2anc
    mpbir2and
end
