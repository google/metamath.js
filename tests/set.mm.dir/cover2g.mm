include "wel.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "cuni.mm"
include "wral.mm"
include "wceq.mm"
include "cpw.mm"
include "unieq.mm"
include "syl6eqr.mm"
include "rexeq.mm"
include "raleqbidv.mm"
include "pweq.mm"
include "eqeq2d.mm"
include "anbi1d.mm"
include "rexeqbidv.mm"
include "vex.mm"
include "eqid.mm"
include "cover2.mm"
include "vtoclbg.mm"

theorem cover2g
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let vb: setvar b
  assume cover2g.1: |- A = U. B

  disjoint ph x
  disjoint ph z
  disjoint x z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint x y
  disjoint y z
  disjoint A x
  disjoint A z
  disjoint b ph
  disjoint b x
  disjoint b z
  disjoint B b
  disjoint b y
  disjoint A b
  assert |- ( B e. C -> ( A. x e. A E. y e. B ( x e. y /\ ph ) <-> E. z e. ~P B ( U. z = A /\ A. y e. z ph ) ) )

  proof
    vx
    vy
    wel
    wph
    wa
    #
    vy
    vb
    cv
    #
    wrex
    #
    vx
    @1
    cuni
    #
    wral
    vz
    cv
    #
    cuni
    #
    @3
    wceq
    #
    wph
    vy
    @4
    wral
    #
    wa
    #
    vz
    @1
    cpw
    #
    wrex
    @0
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    @5
    cA
    wceq
    #
    @7
    wa
    #
    vz
    cB
    cpw
    #
    wrex
    vb
    cB
    cC
    @1
    cB
    wceq
    #
    @2
    @10
    vx
    @3
    cA
    @14
    @3
    cB
    cuni
    cA
    @1
    cB
    unieq
    cover2g.1
    syl6eqr
    #
    @0
    vy
    @1
    cB
    rexeq
    raleqbidv
    @14
    @8
    @12
    vz
    @9
    @13
    @1
    cB
    pweq
    @14
    @6
    @11
    @7
    @14
    @3
    cA
    @5
    @15
    eqeq2d
    anbi1d
    rexeqbidv
    wph
    vx
    vy
    vz
    @3
    @1
    vb
    vex
    @3
    eqid
    cover2
    vtoclbg
end
