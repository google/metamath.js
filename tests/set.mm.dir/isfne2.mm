include "cfne.mm"
include "wbr.mm"
include "wceq.mm"
include "ctg.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "wcel.mm"
include "cv.mm"
include "wrex.mm"
include "wral.mm"
include "isfne4.mm"
include "dfss3.mm"
include "eltg2b.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "anbi2d.mm"

theorem isfne2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vs: setvar s
  assume isfne.1: |- X = U. A
  assume isfne.2: |- Y = U. B

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint r s
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint B r
  disjoint B s
  disjoint X r
  disjoint X s
  disjoint Y r
  disjoint Y s
  assert |- ( B e. C -> ( A Fne B <-> ( X = Y /\ A. x e. A A. y e. x E. z e. B ( y e. z /\ z C_ x ) ) ) )

  proof
    cA
    cB
    cfne
    wbr
    cX
    cY
    wceq
    #
    cA
    cB
    ctg
    cfv
    #
    wss
    #
    wa
    cB
    cC
    wcel
    #
    @0
    vy
    cv
    vz
    cv
    #
    wcel
    @4
    vx
    cv
    #
    wss
    wa
    vz
    cB
    wrex
    vy
    @5
    wral
    #
    vx
    cA
    wral
    #
    wa
    cA
    cB
    cX
    cY
    isfne.1
    isfne.2
    isfne4
    @3
    @2
    @7
    @0
    @2
    @5
    @1
    wcel
    #
    vx
    cA
    wral
    @3
    @7
    vx
    cA
    @1
    dfss3
    @3
    @8
    @6
    vx
    cA
    vy
    vz
    @5
    cB
    cC
    eltg2b
    ralbidv
    syl5bb
    anbi2d
    syl5bb
end
