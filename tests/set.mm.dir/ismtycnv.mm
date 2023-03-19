include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "wf1o.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "ccnv.mm"
include "cismty.mm"
include "wi.mm"
include "f1ocnv.mm"
include "adantr.mm"
include "f1ocnvdm.mm"
include "ex.mm"
include "anim12d.mm"
include "imdistani.mm"
include "oveq1.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rspc2v.mm"
include "impcom.mm"
include "adantll.mm"
include "syl.mm"
include "f1ocnvfv2.mm"
include "adantrr.mm"
include "adantrl.mm"
include "oveq12d.mm"
include "adantlr.mm"
include "eqtr2d.mm"
include "ralrimivva.mm"
include "jca.mm"
include "a1i.mm"
include "isismty.mm"
include "wb.mm"
include "ancoms.mm"
include "3imtr4d.mm"

theorem ismtycnv
  let cF: class F
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( M e. ( *Met ` X ) /\ N e. ( *Met ` Y ) ) -> ( F e. ( M Ismty N ) -> `' F e. ( N Ismty M ) ) )

  proof
    cM
    cX
    cxmt
    cfv
    wcel
    #
    cN
    cY
    cxmt
    cfv
    wcel
    #
    wa
    #
    cX
    cY
    cF
    wf1o
    #
    vx
    cv
    #
    vy
    cv
    #
    cM
    co
    #
    @4
    cF
    cfv
    #
    @5
    cF
    cfv
    #
    cN
    co
    #
    wceq
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    wa
    #
    cY
    cX
    cF
    ccnv
    #
    wf1o
    #
    vu
    cv
    #
    vv
    cv
    #
    cN
    co
    #
    @15
    @13
    cfv
    #
    @16
    @13
    cfv
    #
    cM
    co
    #
    wceq
    #
    vv
    cY
    wral
    vu
    cY
    wral
    #
    wa
    #
    cF
    cM
    cN
    cismty
    co
    wcel
    @13
    cN
    cM
    cismty
    co
    wcel
    #
    @12
    @23
    wi
    @2
    @12
    @14
    @22
    @3
    @14
    @11
    cX
    cY
    cF
    f1ocnv
    adantr
    @12
    @21
    vu
    vv
    cY
    cY
    @12
    @15
    cY
    wcel
    #
    @16
    cY
    wcel
    #
    wa
    #
    wa
    #
    @20
    @18
    cF
    cfv
    #
    @19
    cF
    cfv
    #
    cN
    co
    #
    @17
    @28
    @12
    @18
    cX
    wcel
    #
    @19
    cX
    wcel
    #
    wa
    #
    wa
    @20
    @31
    wceq
    #
    @12
    @27
    @34
    @3
    @27
    @34
    wi
    @11
    @3
    @25
    @32
    @26
    @33
    @3
    @25
    @32
    cX
    cY
    @15
    cF
    f1ocnvdm
    ex
    @3
    @26
    @33
    cX
    cY
    @16
    cF
    f1ocnvdm
    ex
    anim12d
    adantr
    imdistani
    @11
    @34
    @35
    @3
    @34
    @11
    @35
    @10
    @35
    @18
    @5
    cM
    co
    #
    @29
    @8
    cN
    co
    #
    wceq
    vx
    vy
    @18
    @19
    cX
    cX
    @4
    @18
    wceq
    #
    @6
    @36
    @9
    @37
    @4
    @18
    @5
    cM
    oveq1
    @38
    @7
    @29
    @8
    cN
    @4
    @18
    cF
    fveq2
    oveq1d
    eqeq12d
    @5
    @19
    wceq
    #
    @36
    @20
    @37
    @31
    @5
    @19
    @18
    cM
    oveq2
    @39
    @8
    @30
    @29
    cN
    @5
    @19
    cF
    fveq2
    oveq2d
    eqeq12d
    rspc2v
    impcom
    adantll
    syl
    @3
    @27
    @31
    @17
    wceq
    @11
    @3
    @27
    wa
    @29
    @15
    @30
    @16
    cN
    @3
    @25
    @29
    @15
    wceq
    @26
    cX
    cY
    @15
    cF
    f1ocnvfv2
    adantrr
    @3
    @26
    @30
    @16
    wceq
    @25
    cX
    cY
    @16
    cF
    f1ocnvfv2
    adantrl
    oveq12d
    adantlr
    eqtr2d
    ralrimivva
    jca
    a1i
    vx
    vy
    cF
    cM
    cN
    cX
    cY
    isismty
    @1
    @0
    @24
    @23
    wb
    vu
    vv
    @13
    cN
    cM
    cY
    cX
    isismty
    ancoms
    3imtr4d
end
