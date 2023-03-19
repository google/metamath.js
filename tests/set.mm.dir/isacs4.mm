include "cacs.mm"
include "cfv.mm"
include "wcel.mm"
include "cmre.mm"
include "cv.mm"
include "cipo.mm"
include "cdrs.mm"
include "cuni.mm"
include "cima.mm"
include "wceq.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "wa.mm"
include "isacs3lem.mm"
include "isacs4lem.mm"
include "syl.mm"
include "cfn.mm"
include "cin.mm"
include "isacs5lem.mm"
include "isacs5.mm"
include "sylibr.mm"
include "impbii.mm"

theorem isacs4
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
  assert |- ( C e. ( ACS ` X ) <-> ( C e. ( Moore ` X ) /\ A. s e. ~P ~P X ( ( toInc ` s ) e. Dirset -> ( F ` U. s ) = U. ( F " s ) ) ) )

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
    cipo
    cfv
    cdrs
    wcel
    @2
    cuni
    cF
    cfv
    cF
    @2
    cima
    cuni
    wceq
    wi
    vs
    cX
    cpw
    #
    cpw
    wral
    wa
    #
    @0
    @1
    vt
    cv
    #
    cipo
    cfv
    cdrs
    wcel
    @5
    cuni
    cC
    wcel
    wi
    vt
    cC
    cpw
    wral
    wa
    @4
    cC
    cX
    vt
    isacs3lem
    vs
    cC
    cF
    cX
    vt
    acsdrscl.f
    isacs4lem
    syl
    @4
    @1
    @5
    cF
    cfv
    cF
    @5
    cpw
    cfn
    cin
    cima
    cuni
    wceq
    vt
    @3
    wral
    wa
    @0
    vs
    cC
    cF
    cX
    vt
    acsdrscl.f
    isacs5lem
    cC
    cF
    cX
    vt
    acsdrscl.f
    isacs5
    sylibr
    impbii
end
