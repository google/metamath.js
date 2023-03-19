include "cmap.mm"
include "co.mm"
include "wf.mm"
include "cxp.mm"
include "cunc.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "ffvelrn.mm"
include "elmapi.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "anasss.mm"
include "ralrimivva.mm"
include "wceq.mm"
include "coprab.mm"
include "wbr.mm"
include "df-unc.mm"
include "cdm.mm"
include "cop.mm"
include "df-br.mm"
include "elfvdm.mm"
include "sylbi.mm"
include "fdm.mm"
include "eleq2d.mm"
include "syl5ib.mm"
include "pm4.71rd.mm"
include "wfun.mm"
include "wb.mm"
include "elmapfun.mm"
include "funbrfv2b.mm"
include "3syl.mm"
include "eqcom.mm"
include "a1i.mm"
include "anbi12d.mm"
include "bitrd.mm"
include "pm5.32da.mm"
include "anass.mm"
include "syl6bbr.mm"
include "oprabbidv.mm"
include "syl5eq.mm"
include "feq1d.mm"
include "cmpt2.mm"
include "df-mpt2.mm"
include "eqcomi.mm"
include "fmpt2.mm"
include "mpbird.mm"

theorem uncf
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cV: class V
  let cW: class W


  assert |- ( F : A --> ( C ^m B ) -> uncurry F : ( A X. B ) --> C )

  proof
    cA
    cC
    cB
    cmap
    co
    #
    cF
    wf
    #
    cA
    cB
    cxp
    #
    cC
    cF
    cunc
    #
    wf
    #
    vy
    cv
    #
    vx
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cC
    wcel
    #
    vy
    cB
    wral
    vx
    cA
    wral
    #
    @1
    @9
    vx
    vy
    cA
    cB
    @1
    @6
    cA
    wcel
    #
    @5
    cB
    wcel
    #
    @9
    @1
    @11
    wa
    #
    cB
    cC
    @5
    @7
    @13
    @7
    @0
    wcel
    #
    cB
    cC
    @7
    wf
    #
    cA
    @0
    @6
    cF
    ffvelrn
    #
    @7
    cC
    cB
    elmapi
    #
    syl
    ffvelrnda
    anasss
    ralrimivva
    @1
    @4
    @2
    cC
    @11
    @12
    wa
    vz
    cv
    #
    @8
    wceq
    #
    wa
    #
    vx
    vy
    vz
    coprab
    #
    wf
    @10
    @1
    @2
    cC
    @3
    @21
    @1
    @3
    @5
    @18
    @7
    wbr
    #
    vx
    vy
    vz
    coprab
    @21
    vx
    vy
    vz
    cF
    df-unc
    @1
    @22
    @20
    vx
    vy
    vz
    @1
    @22
    @11
    @12
    @19
    wa
    #
    wa
    #
    @20
    @1
    @22
    @11
    @22
    wa
    @24
    @1
    @22
    @11
    @22
    @6
    cF
    cdm
    #
    wcel
    #
    @1
    @11
    @22
    @5
    @18
    cop
    #
    @7
    wcel
    @26
    @5
    @18
    @7
    df-br
    @27
    @6
    cF
    elfvdm
    sylbi
    @1
    @25
    cA
    @6
    cA
    @0
    cF
    fdm
    eleq2d
    syl5ib
    pm4.71rd
    @1
    @11
    @22
    @23
    @13
    @22
    @5
    @7
    cdm
    #
    wcel
    #
    @8
    @18
    wceq
    #
    wa
    #
    @23
    @13
    @14
    @7
    wfun
    @22
    @31
    wb
    @16
    @7
    cC
    cB
    elmapfun
    @5
    @18
    @7
    funbrfv2b
    3syl
    @13
    @29
    @12
    @30
    @19
    @13
    @28
    cB
    @5
    @13
    @14
    @15
    @28
    cB
    wceq
    @16
    @17
    cB
    cC
    @7
    fdm
    3syl
    eleq2d
    @30
    @19
    wb
    @13
    @8
    @18
    eqcom
    a1i
    anbi12d
    bitrd
    pm5.32da
    bitrd
    @11
    @12
    @19
    anass
    syl6bbr
    oprabbidv
    syl5eq
    feq1d
    vx
    vy
    cA
    cB
    @8
    cC
    @21
    vx
    vy
    cA
    cB
    @8
    cmpt2
    @21
    vx
    vy
    vz
    cA
    cB
    @8
    df-mpt2
    eqcomi
    fmpt2
    syl6bbr
    mpbird
end
