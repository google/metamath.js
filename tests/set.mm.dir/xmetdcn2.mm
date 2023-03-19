include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "cxp.mm"
include "cxr.mm"
include "wf.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "xmetf.mm"
include "c2.mm"
include "cdiv.mm"
include "rphalfcl.mm"
include "adantl.mm"
include "simp-4l.mm"
include "simplrl.mm"
include "ad2antrr.mm"
include "simplrr.mm"
include "simpllr.mm"
include "simprl.mm"
include "simprr.mm"
include "metdcnlem.mm"
include "ex.mm"
include "ralrimivva.mm"
include "wceq.mm"
include "breq2.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "2ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "wb.mm"
include "id.mm"
include "xrsxmet.mm"
include "a1i.mm"
include "txmetcn.mm"
include "mpd3an23.mm"
include "mpbir2and.mm"

theorem xmetdcn2
  let cC: class C
  let cD: class D
  let cJ: class J
  let cK: class K
  let cX: class X
  let vr: setvar r
  let vs: setvar s
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume xmetdcn2.1: |- J = ( MetOpen ` D )
  assume xmetdcn2.2: |- C = ( dist ` RR*s )
  assume xmetdcn2.3: |- K = ( MetOpen ` C )


  assert |- ( D e. ( *Met ` X ) -> D e. ( ( J tX J ) Cn K ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cD
    cJ
    cJ
    ctx
    co
    cK
    ccn
    co
    wcel
    #
    cX
    cX
    cxp
    cxr
    cD
    wf
    #
    vx
    cv
    #
    vz
    cv
    #
    cD
    co
    #
    vs
    cv
    #
    clt
    wbr
    #
    vy
    cv
    #
    vw
    cv
    #
    cD
    co
    #
    @6
    clt
    wbr
    #
    wa
    #
    @3
    @8
    cD
    co
    @4
    @9
    cD
    co
    cC
    co
    vr
    cv
    #
    clt
    wbr
    #
    wi
    #
    vw
    cX
    wral
    vz
    cX
    wral
    #
    vs
    crp
    wrex
    #
    vr
    crp
    wral
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    cD
    cX
    xmetf
    @0
    @18
    vx
    vy
    cX
    cX
    @0
    @3
    cX
    wcel
    #
    @8
    cX
    wcel
    #
    wa
    #
    wa
    #
    @17
    vr
    crp
    @23
    @13
    crp
    wcel
    #
    wa
    #
    @13
    c2
    cdiv
    co
    #
    crp
    wcel
    #
    @5
    @26
    clt
    wbr
    #
    @10
    @26
    clt
    wbr
    #
    wa
    #
    @14
    wi
    #
    vw
    cX
    wral
    vz
    cX
    wral
    #
    @17
    @24
    @27
    @23
    @13
    rphalfcl
    adantl
    @25
    @31
    vz
    vw
    cX
    cX
    @25
    @4
    cX
    wcel
    #
    @9
    cX
    wcel
    #
    wa
    #
    wa
    #
    @30
    @14
    @36
    @30
    wa
    @3
    @8
    cC
    cD
    @13
    cJ
    cK
    cX
    @4
    @9
    xmetdcn2.1
    xmetdcn2.2
    xmetdcn2.3
    @0
    @22
    @24
    @35
    @30
    simp-4l
    @25
    @20
    @35
    @30
    @0
    @20
    @21
    @24
    simplrl
    ad2antrr
    @25
    @21
    @35
    @30
    @0
    @20
    @21
    @24
    simplrr
    ad2antrr
    @23
    @24
    @35
    @30
    simpllr
    @25
    @33
    @34
    @30
    simplrl
    @25
    @33
    @34
    @30
    simplrr
    @36
    @28
    @29
    simprl
    @36
    @28
    @29
    simprr
    metdcnlem
    ex
    ralrimivva
    @16
    @32
    vs
    @26
    crp
    @6
    @26
    wceq
    #
    @15
    @31
    vz
    vw
    cX
    cX
    @37
    @12
    @30
    @14
    @37
    @7
    @28
    @11
    @29
    @6
    @26
    @5
    clt
    breq2
    @6
    @26
    @10
    clt
    breq2
    anbi12d
    imbi1d
    2ralbidv
    rspcev
    syl2anc
    ralrimiva
    ralrimivva
    @0
    @0
    cC
    cxr
    cxmt
    cfv
    wcel
    #
    @1
    @2
    @19
    wa
    wb
    @0
    id
    @38
    @0
    cC
    xmetdcn2.2
    xrsxmet
    a1i
    vx
    vy
    vr
    vs
    vw
    vz
    cD
    cD
    cC
    cD
    cJ
    cJ
    cK
    cX
    cX
    cxr
    xmetdcn2.1
    xmetdcn2.1
    xmetdcn2.3
    txmetcn
    mpd3an23
    mpbir2and
end
