include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "wfo.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cqtop.mm"
include "co.mm"
include "wral.mm"
include "ccom.mm"
include "ccn.mm"
include "wss.mm"
include "wb.mm"
include "simplll.mm"
include "simplrl.mm"
include "elqtop3.mm"
include "syl2anc.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wceq.mm"
include "simplrr.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "cnvco.mm"
include "imaeq1i.mm"
include "imaco.mm"
include "eqtri.mm"
include "eleq1i.mm"
include "syl6bbr.mm"
include "ralbidva.mm"
include "simprr.mm"
include "fof.mm"
include "ad2antrl.mm"
include "fco.mm"
include "3bitr3d.mm"
include "qtoptopon.mm"
include "ad2ant2r.mm"
include "simplr.mm"
include "iscn.mm"
include "adantr.mm"
include "3bitr4d.mm"

theorem qtopcn
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vf: setvar f
  let vg: setvar g
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let wph: wff ph


  assert |- ( ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Z ) ) /\ ( F : X -onto-> Y /\ G : Y --> Z ) ) -> ( G e. ( ( J qTop F ) Cn K ) <-> ( G o. F ) e. ( J Cn K ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cZ
    ctopon
    cfv
    wcel
    #
    wa
    #
    cX
    cY
    cF
    wfo
    #
    cY
    cZ
    cG
    wf
    #
    wa
    #
    wa
    #
    @4
    cG
    ccnv
    #
    vx
    cv
    #
    cima
    #
    cJ
    cF
    cqtop
    co
    #
    wcel
    #
    vx
    cK
    wral
    #
    wa
    #
    cX
    cZ
    cG
    cF
    ccom
    #
    wf
    #
    @14
    ccnv
    #
    @8
    cima
    #
    cJ
    wcel
    #
    vx
    cK
    wral
    #
    wa
    #
    cG
    @10
    cK
    ccn
    co
    wcel
    #
    @14
    cJ
    cK
    ccn
    co
    wcel
    #
    @6
    @12
    @19
    @13
    @20
    @6
    @11
    @18
    vx
    cK
    @6
    @8
    cK
    wcel
    #
    wa
    #
    @11
    cF
    ccnv
    #
    @9
    cima
    #
    cJ
    wcel
    #
    @18
    @24
    @11
    @9
    cY
    wss
    #
    @27
    wa
    #
    @27
    @24
    @0
    @3
    @11
    @29
    wb
    @0
    @1
    @5
    @23
    simplll
    @2
    @3
    @4
    @23
    simplrl
    @9
    cF
    cJ
    cX
    cY
    elqtop3
    syl2anc
    @24
    @28
    @27
    @24
    cG
    cdm
    #
    @9
    cY
    cG
    @8
    cnvimass
    @24
    @4
    @30
    cY
    wceq
    @2
    @3
    @4
    @23
    simplrr
    cY
    cZ
    cG
    fdm
    syl
    syl5sseq
    biantrurd
    bitr4d
    @17
    @26
    cJ
    @17
    @25
    @7
    ccom
    #
    @8
    cima
    @26
    @16
    @31
    @8
    cG
    cF
    cnvco
    imaeq1i
    @25
    @7
    @8
    imaco
    eqtri
    eleq1i
    syl6bbr
    ralbidva
    @6
    @4
    @12
    @2
    @3
    @4
    simprr
    #
    biantrurd
    @6
    @15
    @19
    @6
    @4
    cX
    cY
    cF
    wf
    #
    @15
    @32
    @3
    @33
    @2
    @4
    cX
    cY
    cF
    fof
    ad2antrl
    cX
    cY
    cZ
    cG
    cF
    fco
    syl2anc
    biantrurd
    3bitr3d
    @6
    @10
    cY
    ctopon
    cfv
    wcel
    #
    @1
    @21
    @13
    wb
    @0
    @3
    @34
    @1
    @4
    cF
    cJ
    cX
    cY
    qtoptopon
    ad2ant2r
    @0
    @1
    @5
    simplr
    vx
    cG
    @10
    cK
    cY
    cZ
    iscn
    syl2anc
    @2
    @22
    @20
    wb
    @5
    vx
    @14
    cJ
    cK
    cX
    cZ
    iscn
    adantr
    3bitr4d
end
