include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cipo.mm"
include "cdrs.mm"
include "cuni.mm"
include "cima.mm"
include "wceq.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "cfn.mm"
include "cin.mm"
include "wa.mm"
include "unifpw.mm"
include "fveq2i.mm"
include "cvv.mm"
include "vex.mm"
include "fpwipodrs.mm"
include "mp1i.mm"
include "wss.mm"
include "inss1.mm"
include "elpwi.mm"
include "sspwb.mm"
include "sylib.mm"
include "adantl.mm"
include "syl5ss.mm"
include "vpwex.mm"
include "inex1.mm"
include "elpw.mm"
include "sylibr.mm"
include "adantlr.mm"
include "simplr.mm"
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
include "mpd.mm"
include "syl5eqr.mm"
include "ralrimiva.mm"
include "ex.mm"
include "imdistani.mm"

theorem isacs5lem
  let vt: setvar t
  let cC: class C
  let cF: class F
  let cX: class X
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let cY: class Y
  let cS: class S
  assume acsdrscl.f: |- F = ( mrCls ` C )

  disjoint C s
  disjoint C t
  disjoint s t
  disjoint F s
  disjoint F t
  disjoint X s
  disjoint X t
  disjoint C x
  disjoint C y
  disjoint s x
  disjoint s y
  disjoint t x
  disjoint t y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint X x
  disjoint X y
  disjoint Y s
  disjoint Y t
  disjoint S s
  assert |- ( ( C e. ( Moore ` X ) /\ A. t e. ~P ~P X ( ( toInc ` t ) e. Dirset -> ( F ` U. t ) = U. ( F " t ) ) ) -> ( C e. ( Moore ` X ) /\ A. s e. ~P X ( F ` s ) = U. ( F " ( ~P s i^i Fin ) ) ) )

  proof
    cC
    cX
    cmre
    cfv
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
    @1
    cuni
    #
    cF
    cfv
    #
    cF
    @1
    cima
    #
    cuni
    #
    wceq
    #
    wi
    #
    vt
    cX
    cpw
    #
    cpw
    #
    wral
    #
    vs
    cv
    #
    cF
    cfv
    #
    cF
    @13
    cpw
    #
    cfn
    cin
    #
    cima
    #
    cuni
    #
    wceq
    #
    vs
    @10
    wral
    #
    @0
    @12
    @20
    @0
    @12
    wa
    #
    @19
    vs
    @10
    @21
    @13
    @10
    wcel
    #
    wa
    #
    @14
    @16
    cuni
    #
    cF
    cfv
    #
    @18
    @24
    @13
    cF
    @13
    unifpw
    fveq2i
    @23
    @16
    cipo
    cfv
    #
    cdrs
    wcel
    #
    @25
    @18
    wceq
    #
    @13
    cvv
    wcel
    @27
    @23
    vs
    vex
    @13
    cvv
    fpwipodrs
    mp1i
    @23
    @16
    @11
    wcel
    #
    @12
    @27
    @28
    wi
    #
    @0
    @22
    @29
    @12
    @0
    @22
    wa
    #
    @16
    @10
    wss
    @29
    @31
    @16
    @15
    @10
    @15
    cfn
    inss1
    @22
    @15
    @10
    wss
    #
    @0
    @22
    @13
    cX
    wss
    @32
    @13
    cX
    elpwi
    @13
    cX
    sspwb
    sylib
    adantl
    syl5ss
    @16
    @10
    @15
    cfn
    vs
    vpwex
    inex1
    elpw
    sylibr
    adantlr
    @0
    @12
    @22
    simplr
    @9
    @30
    vt
    @16
    @11
    @1
    @16
    wceq
    #
    @3
    @27
    @8
    @28
    @33
    @2
    @26
    cdrs
    @1
    @16
    cipo
    fveq2
    eleq1d
    @33
    @5
    @25
    @7
    @18
    @33
    @4
    @24
    cF
    @1
    @16
    unieq
    fveq2d
    @33
    @6
    @17
    @1
    @16
    cF
    imaeq2
    unieqd
    eqeq12d
    imbi12d
    rspcva
    syl2anc
    mpd
    syl5eqr
    ralrimiva
    ex
    imdistani
end
