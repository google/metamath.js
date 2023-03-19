include "chil.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wral.mm"
include "crab.mm"
include "wa.mm"
include "ocval.mm"
include "eleq2d.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem ocel
  let vx: setvar x
  let cA: class A
  let cH: class H
  let vy: setvar y
  let vz: setvar z
  let cB: class B

  disjoint H x
  disjoint A x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint H y
  disjoint H z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  assert |- ( H C_ ~H -> ( A e. ( _|_ ` H ) <-> ( A e. ~H /\ A. x e. H ( A .ih x ) = 0 ) ) )

  proof
    cH
    chil
    wss
    #
    cA
    cH
    cort
    cfv
    #
    wcel
    cA
    vy
    cv
    #
    vx
    cv
    #
    csp
    co
    #
    cc0
    wceq
    #
    vx
    cH
    wral
    #
    vy
    chil
    crab
    #
    wcel
    cA
    chil
    wcel
    cA
    @3
    csp
    co
    #
    cc0
    wceq
    #
    vx
    cH
    wral
    #
    wa
    @0
    @1
    @7
    cA
    vy
    vx
    cH
    ocval
    eleq2d
    @6
    @10
    vy
    cA
    chil
    @2
    cA
    wceq
    #
    @5
    @9
    vx
    cH
    @11
    @4
    @8
    cc0
    @2
    cA
    @3
    csp
    oveq1
    eqeq1d
    ralbidv
    elrab
    syl6bb
end
