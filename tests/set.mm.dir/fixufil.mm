include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cpw.mm"
include "crab.mm"
include "cfil.mm"
include "cfv.mm"
include "cdif.mm"
include "wo.mm"
include "wral.mm"
include "cufil.mm"
include "csn.mm"
include "cfg.mm"
include "co.mm"
include "cfbas.mm"
include "wceq.mm"
include "uffix.mm"
include "simprd.mm"
include "simpld.mm"
include "fgcl.mm"
include "syl.mm"
include "eqeltrd.mm"
include "cun.mm"
include "undif2.mm"
include "wss.mm"
include "elpwi.mm"
include "ssequn1.mm"
include "sylib.mm"
include "syl5req.mm"
include "eleq2d.mm"
include "biimpac.mm"
include "elun.mm"
include "adantll.mm"
include "wb.mm"
include "ibar.mm"
include "adantl.mm"
include "difss.mm"
include "elpw2g.mm"
include "mpbiri.mm"
include "ad2antrr.mm"
include "biantrurd.mm"
include "orbi12d.mm"
include "mpbid.mm"
include "ralrimiva.mm"
include "eleq2.mm"
include "elrab.mm"
include "orbi12i.mm"
include "ralbii.mm"
include "sylibr.mm"
include "isufil.mm"
include "sylanbrc.mm"

theorem fixufil
  let vx: setvar x
  let cA: class A
  let cV: class V
  let cX: class X
  let vy: setvar y

  disjoint A x
  disjoint X x
  disjoint V x
  disjoint x y
  disjoint A y
  disjoint X y
  disjoint V y
  assert |- ( ( X e. V /\ A e. X ) -> { x e. ~P X | A e. x } e. ( UFil ` X ) )

  proof
    cX
    cV
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cA
    vx
    cv
    #
    wcel
    #
    vx
    cX
    cpw
    #
    crab
    #
    cX
    cfil
    cfv
    #
    wcel
    vy
    cv
    #
    @6
    wcel
    #
    cX
    @8
    cdif
    #
    @6
    wcel
    #
    wo
    #
    vy
    @5
    wral
    #
    @6
    cX
    cufil
    cfv
    wcel
    @2
    @6
    cX
    cA
    csn
    csn
    #
    cfg
    co
    #
    @7
    @2
    @14
    cX
    cfbas
    cfv
    wcel
    #
    @6
    @15
    wceq
    #
    vx
    cA
    cV
    cX
    uffix
    #
    simprd
    @2
    @16
    @15
    @7
    wcel
    @2
    @16
    @17
    @18
    simpld
    @14
    cX
    fgcl
    syl
    eqeltrd
    @2
    @8
    @5
    wcel
    #
    cA
    @8
    wcel
    #
    wa
    #
    @10
    @5
    wcel
    #
    cA
    @10
    wcel
    #
    wa
    #
    wo
    #
    vy
    @5
    wral
    @13
    @2
    @25
    vy
    @5
    @2
    @19
    wa
    #
    @20
    @23
    wo
    #
    @25
    @1
    @19
    @27
    @0
    @1
    @19
    wa
    cA
    @8
    @10
    cun
    #
    wcel
    #
    @27
    @19
    @1
    @29
    @19
    cX
    @28
    cA
    @19
    @28
    @8
    cX
    cun
    #
    cX
    @8
    cX
    undif2
    @19
    @8
    cX
    wss
    @30
    cX
    wceq
    @8
    cX
    elpwi
    @8
    cX
    ssequn1
    sylib
    syl5req
    eleq2d
    biimpac
    cA
    @8
    @10
    elun
    sylib
    adantll
    @26
    @20
    @21
    @23
    @24
    @19
    @20
    @21
    wb
    @2
    @19
    @20
    ibar
    adantl
    @26
    @22
    @23
    @0
    @22
    @1
    @19
    @0
    @22
    @10
    cX
    wss
    cX
    @8
    difss
    @10
    cX
    cV
    elpw2g
    mpbiri
    ad2antrr
    biantrurd
    orbi12d
    mpbid
    ralrimiva
    @12
    @25
    vy
    @5
    @9
    @21
    @11
    @24
    @4
    @20
    vx
    @8
    @5
    @3
    @8
    cA
    eleq2
    elrab
    @4
    @23
    vx
    @10
    @5
    @3
    @10
    cA
    eleq2
    elrab
    orbi12i
    ralbii
    sylibr
    vy
    @6
    cX
    isufil
    sylanbrc
end
