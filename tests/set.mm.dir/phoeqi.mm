include "cv.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wf.mm"
include "wa.mm"
include "ralcom.mm"
include "wcel.mm"
include "wb.mm"
include "ffvelrn.mm"
include "ip2eqi.mm"
include "syl2an.mm"
include "anandirs.mm"
include "ralbidva.mm"
include "wfn.mm"
include "ffn.mm"
include "eqfnfv.mm"
include "bitr4d.mm"
include "syl5bb.mm"

theorem phoeqi
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cS: class S
  let cT: class T
  let cU: class U
  let cX: class X
  let cY: class Y
  let cA: class A
  let cB: class B
  let vs: setvar s
  let vt: setvar t
  let cQ: class Q
  assume ip2eqi.1: |- X = ( BaseSet ` U )
  assume ip2eqi.7: |- P = ( .iOLD ` U )
  assume ip2eqi.u: |- U e. CPreHilOLD

  disjoint P x
  disjoint x y
  disjoint S x
  disjoint S y
  disjoint T x
  disjoint T y
  disjoint U x
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint A x
  disjoint B x
  disjoint s t
  disjoint s x
  disjoint P s
  disjoint t x
  disjoint P t
  disjoint Q s
  disjoint Q t
  disjoint s y
  disjoint T s
  disjoint t y
  disjoint T t
  disjoint X s
  disjoint X t
  disjoint Y s
  disjoint Y t
  assert |- ( ( S : Y --> X /\ T : Y --> X ) -> ( A. x e. X A. y e. Y ( x P ( S ` y ) ) = ( x P ( T ` y ) ) <-> S = T ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cS
    cfv
    #
    cP
    co
    @0
    @1
    cT
    cfv
    #
    cP
    co
    wceq
    #
    vy
    cY
    wral
    vx
    cX
    wral
    @4
    vx
    cX
    wral
    #
    vy
    cY
    wral
    #
    cY
    cX
    cS
    wf
    #
    cY
    cX
    cT
    wf
    #
    wa
    #
    cS
    cT
    wceq
    #
    @4
    vx
    vy
    cX
    cY
    ralcom
    @9
    @6
    @2
    @3
    wceq
    #
    vy
    cY
    wral
    #
    @10
    @9
    @5
    @11
    vy
    cY
    @7
    @8
    @1
    cY
    wcel
    #
    @5
    @11
    wb
    #
    @7
    @13
    wa
    @2
    cX
    wcel
    @3
    cX
    wcel
    @14
    @8
    @13
    wa
    cY
    cX
    @1
    cS
    ffvelrn
    cY
    cX
    @1
    cT
    ffvelrn
    vx
    @2
    @3
    cP
    cU
    cX
    ip2eqi.1
    ip2eqi.7
    ip2eqi.u
    ip2eqi
    syl2an
    anandirs
    ralbidva
    @7
    cS
    cY
    wfn
    cT
    cY
    wfn
    @10
    @12
    wb
    @8
    cY
    cX
    cS
    ffn
    cY
    cX
    cT
    ffn
    vy
    cY
    cS
    cT
    eqfnfv
    syl2an
    bitr4d
    syl5bb
end
