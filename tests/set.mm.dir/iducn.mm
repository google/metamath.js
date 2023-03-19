include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "cucn.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of.mm"
include "mp1i.mm"
include "wa.mm"
include "simpr.mm"
include "fvresi.mm"
include "breqan12d.mm"
include "biimprd.mm"
include "adantl.mm"
include "ralrimivva.mm"
include "weq.mm"
include "breq.mm"
include "imbi1d.mm"
include "2ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "wb.mm"
include "isucn.mm"
include "anidms.mm"
include "mpbir2and.mm"

theorem iducn
  let cU: class U
  let cX: class X
  let vr: setvar r
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y


  assert |- ( U e. ( UnifOn ` X ) -> ( _I |` X ) e. ( U uCn U ) )

  proof
    cU
    cX
    cust
    cfv
    wcel
    #
    cid
    cX
    cres
    #
    cU
    cU
    cucn
    co
    wcel
    #
    cX
    cX
    @1
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
    @4
    @1
    cfv
    #
    @5
    @1
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
    cU
    wral
    #
    cX
    cX
    @1
    wf1o
    @3
    @0
    cX
    f1oi
    cX
    cX
    @1
    f1of
    mp1i
    @0
    @14
    vs
    cU
    @0
    @10
    cU
    wcel
    #
    wa
    #
    @16
    @4
    @5
    @10
    wbr
    #
    @11
    wi
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    @14
    @0
    @16
    simpr
    @17
    @19
    vx
    vy
    cX
    cX
    @4
    cX
    wcel
    #
    @5
    cX
    wcel
    #
    wa
    #
    @19
    @17
    @23
    @11
    @18
    @21
    @22
    @8
    @4
    @9
    @5
    @10
    cX
    @4
    fvresi
    cX
    @5
    fvresi
    breqan12d
    biimprd
    adantl
    ralrimivva
    @13
    @20
    vr
    @10
    cU
    vr
    vs
    weq
    #
    @12
    @19
    vx
    vy
    cX
    cX
    @24
    @7
    @18
    @11
    @4
    @5
    @6
    @10
    breq
    imbi1d
    2ralbidv
    rspcev
    syl2anc
    ralrimiva
    @0
    @2
    @3
    @15
    wa
    wb
    vx
    vy
    cU
    @1
    cU
    cX
    cX
    vs
    vr
    isucn
    anidms
    mpbir2and
end
