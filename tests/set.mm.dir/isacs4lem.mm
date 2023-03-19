include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cipo.mm"
include "cdrs.mm"
include "cuni.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "cima.mm"
include "wceq.mm"
include "wa.mm"
include "wss.mm"
include "simpll.mm"
include "elpwi.mm"
include "ad2antrl.mm"
include "mrcuni.mm"
include "syl2anc.mm"
include "cvv.mm"
include "wfn.mm"
include "mrcf.mm"
include "ffnd.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "mrcssd.mm"
include "cmrc.mm"
include "fvex.mm"
include "eqeltri.mm"
include "imaex.mm"
include "a1i.mm"
include "ipodrsima.mm"
include "adantlr.mm"
include "crn.mm"
include "imassrn.mm"
include "wf.mm"
include "frn.mm"
include "syl.mm"
include "syl5ss.mm"
include "elpw.mm"
include "sylibr.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "unieq.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "mpd.mm"
include "mrcid.mm"
include "eqtrd.mm"
include "exp32.mm"
include "ralrimiv.mm"
include "ex.mm"
include "imdistani.mm"

theorem isacs4lem
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
  assert |- ( ( C e. ( Moore ` X ) /\ A. s e. ~P C ( ( toInc ` s ) e. Dirset -> U. s e. C ) ) -> ( C e. ( Moore ` X ) /\ A. t e. ~P ~P X ( ( toInc ` t ) e. Dirset -> ( F ` U. t ) = U. ( F " t ) ) ) )

  proof
    cC
    cX
    cmre
    cfv
    wcel
    #
    vs
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
    cC
    wcel
    #
    wi
    #
    vs
    cC
    cpw
    #
    wral
    #
    vt
    cv
    #
    cipo
    cfv
    cdrs
    wcel
    #
    @9
    cuni
    cF
    cfv
    #
    cF
    @9
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
    @0
    @8
    @18
    @0
    @8
    wa
    #
    @15
    vt
    @17
    @19
    @9
    @17
    wcel
    #
    @10
    @14
    @19
    @20
    @10
    wa
    #
    wa
    #
    @11
    @13
    cF
    cfv
    #
    @13
    @22
    @0
    @9
    @16
    wss
    #
    @11
    @23
    wceq
    @0
    @8
    @21
    simpll
    #
    @20
    @24
    @19
    @10
    @9
    @16
    elpwi
    #
    ad2antrl
    cC
    @9
    cF
    cX
    acsdrscl.f
    mrcuni
    syl2anc
    @22
    @0
    @13
    cC
    wcel
    #
    @23
    @13
    wceq
    @25
    @22
    @12
    cipo
    cfv
    #
    cdrs
    wcel
    #
    @27
    @0
    @21
    @29
    @8
    @0
    @21
    wa
    #
    vy
    vx
    cX
    @9
    cF
    cvv
    @0
    cF
    @16
    wfn
    @21
    @0
    @16
    cC
    cF
    cC
    cF
    cX
    acsdrscl.f
    mrcf
    #
    ffnd
    adantr
    @30
    vx
    cv
    #
    vy
    cv
    #
    wss
    #
    @33
    cX
    wss
    #
    wa
    #
    wa
    cC
    @32
    cF
    @33
    cX
    @0
    @21
    @36
    simpll
    acsdrscl.f
    @30
    @34
    @35
    simprl
    @30
    @34
    @35
    simprr
    mrcssd
    @0
    @20
    @10
    simprr
    @20
    @24
    @0
    @10
    @26
    ad2antrl
    @12
    cvv
    wcel
    @30
    cF
    @9
    cF
    cC
    cmrc
    cfv
    cvv
    acsdrscl.f
    cC
    cmrc
    fvex
    eqeltri
    imaex
    #
    a1i
    ipodrsima
    adantlr
    @22
    @12
    @7
    wcel
    #
    @8
    @29
    @27
    wi
    #
    @0
    @38
    @8
    @21
    @0
    @12
    cC
    wss
    @38
    @0
    @12
    cF
    crn
    #
    cC
    cF
    @9
    imassrn
    @0
    @16
    cC
    cF
    wf
    @40
    cC
    wss
    @31
    @16
    cC
    cF
    frn
    syl
    syl5ss
    @12
    cC
    @37
    elpw
    sylibr
    ad2antrr
    @0
    @8
    @21
    simplr
    @6
    @39
    vs
    @12
    @7
    @1
    @12
    wceq
    #
    @3
    @29
    @5
    @27
    @41
    @2
    @28
    cdrs
    @1
    @12
    cipo
    fveq2
    eleq1d
    @41
    @4
    @13
    cC
    @1
    @12
    unieq
    eleq1d
    imbi12d
    rspcva
    syl2anc
    mpd
    cC
    @13
    cF
    cX
    acsdrscl.f
    mrcid
    syl2anc
    eqtrd
    exp32
    ralrimiv
    ex
    imdistani
end
