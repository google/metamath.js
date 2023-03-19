include "cacs.mm"
include "cfv.mm"
include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "cipo.mm"
include "cdrs.mm"
include "cuni.mm"
include "cima.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "cdm.mm"
include "cvv.mm"
include "wb.mm"
include "elfvdm.mm"
include "pwexg.mm"
include "elpw2g.mm"
include "3syl.mm"
include "biimpar.mm"
include "cmre.mm"
include "isacs3lem.mm"
include "isacs4lem.mm"
include "syl.mm"
include "simprd.mm"
include "adantr.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "unieq.mm"
include "fveq2d.mm"
include "imaeq2.mm"
include "unieqd.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "3impia.mm"

theorem acsdrscl
  let cC: class C
  let cF: class F
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  assume acsdrscl.f: |- F = ( mrCls ` C )


  assert |- ( ( C e. ( ACS ` X ) /\ Y C_ ~P X /\ ( toInc ` Y ) e. Dirset ) -> ( F ` U. Y ) = U. ( F " Y ) )

  proof
    cC
    cX
    cacs
    cfv
    wcel
    #
    cY
    cX
    cpw
    #
    wss
    #
    cY
    cipo
    cfv
    #
    cdrs
    wcel
    #
    cY
    cuni
    #
    cF
    cfv
    #
    cF
    cY
    cima
    #
    cuni
    #
    wceq
    #
    @0
    @2
    wa
    cY
    @1
    cpw
    #
    wcel
    #
    vt
    cv
    #
    cipo
    cfv
    #
    cdrs
    wcel
    #
    @12
    cuni
    #
    cF
    cfv
    #
    cF
    @12
    cima
    #
    cuni
    #
    wceq
    #
    wi
    #
    vt
    @10
    wral
    #
    @4
    @9
    wi
    #
    @0
    @11
    @2
    @0
    cX
    cacs
    cdm
    #
    wcel
    @1
    cvv
    wcel
    @11
    @2
    wb
    cC
    cX
    cacs
    elfvdm
    cX
    @23
    pwexg
    cY
    @1
    cvv
    elpw2g
    3syl
    biimpar
    @0
    @21
    @2
    @0
    cC
    cX
    cmre
    cfv
    wcel
    #
    @21
    @0
    @24
    vs
    cv
    #
    cipo
    cfv
    cdrs
    wcel
    @25
    cuni
    cC
    wcel
    wi
    vs
    cC
    cpw
    wral
    wa
    @24
    @21
    wa
    cC
    cX
    vs
    isacs3lem
    vt
    cC
    cF
    cX
    vs
    acsdrscl.f
    isacs4lem
    syl
    simprd
    adantr
    @20
    @22
    vt
    cY
    @10
    @12
    cY
    wceq
    #
    @14
    @4
    @19
    @9
    @26
    @13
    @3
    cdrs
    @12
    cY
    cipo
    fveq2
    eleq1d
    @26
    @16
    @6
    @18
    @8
    @26
    @15
    @5
    cF
    @12
    cY
    unieq
    fveq2d
    @26
    @17
    @7
    @12
    cY
    cF
    imaeq2
    unieqd
    eqeq12d
    imbi12d
    rspcva
    syl2anc
    3impia
end
