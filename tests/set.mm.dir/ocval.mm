include "chil.mm"
include "wss.mm"
include "cpw.mm"
include "wcel.mm"
include "cort.mm"
include "cfv.mm"
include "cv.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wral.mm"
include "crab.mm"
include "ax-hilex.mm"
include "elpw2.mm"
include "raleq.mm"
include "rabbidv.mm"
include "df-oc.mm"
include "rabex.mm"
include "fvmpt.mm"
include "sylbir.mm"

theorem ocval
  let vx: setvar x
  let vy: setvar y
  let cH: class H
  let vz: setvar z
  let cA: class A
  let cB: class B

  disjoint x y
  disjoint H x
  disjoint H y
  disjoint x z
  disjoint y z
  disjoint H z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  assert |- ( H C_ ~H -> ( _|_ ` H ) = { x e. ~H | A. y e. H ( x .ih y ) = 0 } )

  proof
    cH
    chil
    wss
    cH
    chil
    cpw
    #
    wcel
    cH
    cort
    cfv
    vx
    cv
    vy
    cv
    csp
    co
    cc0
    wceq
    #
    vy
    cH
    wral
    #
    vx
    chil
    crab
    #
    wceq
    cH
    chil
    ax-hilex
    elpw2
    vz
    cH
    @1
    vy
    vz
    cv
    #
    wral
    #
    vx
    chil
    crab
    @3
    @0
    cort
    @4
    cH
    wceq
    @5
    @2
    vx
    chil
    @1
    vy
    @4
    cH
    raleq
    rabbidv
    vz
    vx
    vy
    df-oc
    @2
    vx
    chil
    ax-hilex
    rabex
    fvmpt
    sylbir
end
