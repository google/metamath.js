include "cfne.mm"
include "wbr.mm"
include "wceq.mm"
include "ctg.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "wcel.mm"
include "cv.mm"
include "cuni.mm"
include "wex.mm"
include "wral.mm"
include "isfne4.mm"
include "dfss3.mm"
include "eltg3.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "anbi2d.mm"

theorem isfne3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vs: setvar s
  let vz: setvar z
  assume isfne.1: |- X = U. A
  assume isfne.2: |- Y = U. B

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint r s
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B r
  disjoint B s
  disjoint B z
  disjoint C z
  disjoint X r
  disjoint X s
  disjoint Y r
  disjoint Y s
  assert |- ( B e. C -> ( A Fne B <-> ( X = Y /\ A. x e. A E. y ( y C_ B /\ x = U. y ) ) ) )

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
    #
    cB
    wss
    vx
    cv
    #
    @4
    cuni
    wceq
    wa
    vy
    wex
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
    @5
    cB
    cC
    eltg3
    ralbidv
    syl5bb
    anbi2d
    syl5bb
end
