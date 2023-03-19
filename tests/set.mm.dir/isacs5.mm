include "cacs.mm"
include "cfv.mm"
include "wcel.mm"
include "cmre.mm"
include "cv.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cima.mm"
include "cuni.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "cipo.mm"
include "cdrs.mm"
include "wi.mm"
include "isacs3lem.mm"
include "isacs4lem.mm"
include "isacs5lem.mm"
include "3syl.mm"
include "wss.mm"
include "wb.mm"
include "simpl.mm"
include "elpwi.mm"
include "mrcidb2.mm"
include "sylan2.mm"
include "adantr.mm"
include "ciun.mm"
include "simpr.mm"
include "wf.mm"
include "wfun.mm"
include "mrcf.mm"
include "ffun.mm"
include "funiunfv.mm"
include "ad2antrr.mm"
include "eqtr4d.mm"
include "sseq1d.mm"
include "iunss.mm"
include "syl6bb.mm"
include "bitrd.mm"
include "ex.mm"
include "ralimdva.mm"
include "imp.mm"
include "isacs2.mm"
include "sylanbrc.mm"
include "impbii.mm"

theorem isacs5
  let cC: class C
  let cF: class F
  let cX: class X
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cY: class Y
  let cS: class S
  assume acsdrscl.f: |- F = ( mrCls ` C )

  disjoint C s
  disjoint F s
  disjoint X s
  disjoint C t
  disjoint C x
  disjoint C y
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint t x
  disjoint t y
  disjoint x y
  disjoint F t
  disjoint F x
  disjoint F y
  disjoint X t
  disjoint X x
  disjoint X y
  disjoint Y s
  disjoint Y t
  disjoint S s
  assert |- ( C e. ( ACS ` X ) <-> ( C e. ( Moore ` X ) /\ A. s e. ~P X ( F ` s ) = U. ( F " ( ~P s i^i Fin ) ) ) )

  proof
    cC
    cX
    cacs
    cfv
    wcel
    #
    cC
    cX
    cmre
    cfv
    wcel
    #
    vs
    cv
    #
    cF
    cfv
    #
    cF
    @2
    cpw
    cfn
    cin
    #
    cima
    cuni
    #
    wceq
    #
    vs
    cX
    cpw
    #
    wral
    #
    wa
    #
    @0
    @1
    @2
    cipo
    cfv
    cdrs
    wcel
    @2
    cuni
    cC
    wcel
    wi
    vs
    cC
    cpw
    wral
    wa
    @1
    vt
    cv
    #
    cipo
    cfv
    cdrs
    wcel
    @10
    cuni
    cF
    cfv
    cF
    @10
    cima
    cuni
    wceq
    wi
    vt
    @7
    cpw
    wral
    wa
    @9
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
    vt
    cC
    cF
    cX
    vs
    acsdrscl.f
    isacs5lem
    3syl
    @9
    @1
    @2
    cC
    wcel
    #
    @10
    cF
    cfv
    #
    @2
    wss
    vt
    @4
    wral
    #
    wb
    #
    vs
    @7
    wral
    #
    @0
    @1
    @8
    simpl
    @1
    @8
    @15
    @1
    @6
    @14
    vs
    @7
    @1
    @2
    @7
    wcel
    #
    wa
    #
    @6
    @14
    @17
    @6
    wa
    #
    @11
    @3
    @2
    wss
    #
    @13
    @17
    @11
    @19
    wb
    #
    @6
    @16
    @1
    @2
    cX
    wss
    @20
    @2
    cX
    elpwi
    cC
    @2
    cF
    cX
    acsdrscl.f
    mrcidb2
    sylan2
    adantr
    @18
    @19
    vt
    @4
    @12
    ciun
    #
    @2
    wss
    @13
    @18
    @3
    @21
    @2
    @18
    @3
    @5
    @21
    @17
    @6
    simpr
    @1
    @21
    @5
    wceq
    #
    @16
    @6
    @1
    @7
    cC
    cF
    wf
    cF
    wfun
    @22
    cC
    cF
    cX
    acsdrscl.f
    mrcf
    @7
    cC
    cF
    ffun
    vt
    @4
    cF
    funiunfv
    3syl
    ad2antrr
    eqtr4d
    sseq1d
    vt
    @4
    @12
    @2
    iunss
    syl6bb
    bitrd
    ex
    ralimdva
    imp
    vt
    cC
    cF
    cX
    vs
    acsdrscl.f
    isacs2
    sylanbrc
    impbii
end
