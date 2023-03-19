include "chil.mm"
include "cpw.mm"
include "wss.mm"
include "wcel.mm"
include "chsup.mm"
include "cfv.mm"
include "cuni.mm"
include "cort.mm"
include "wceq.mm"
include "ax-hilex.mm"
include "pwex.mm"
include "elpw2.mm"
include "cv.mm"
include "unieq.mm"
include "fveq2d.mm"
include "df-chsup.mm"
include "fvex.mm"
include "fvmpt.mm"
include "sylbir.mm"

theorem hsupval
  let cA: class A
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A C_ ~P ~H -> ( \/H ` A ) = ( _|_ ` ( _|_ ` U. A ) ) )

  proof
    cA
    chil
    cpw
    #
    wss
    cA
    @0
    cpw
    #
    wcel
    cA
    chsup
    cfv
    cA
    cuni
    #
    cort
    cfv
    #
    cort
    cfv
    #
    wceq
    cA
    @0
    chil
    ax-hilex
    pwex
    elpw2
    vx
    cA
    vx
    cv
    #
    cuni
    #
    cort
    cfv
    #
    cort
    cfv
    @4
    @1
    chsup
    @5
    cA
    wceq
    #
    @7
    @3
    cort
    @8
    @6
    @2
    cort
    @5
    cA
    unieq
    fveq2d
    fveq2d
    vx
    df-chsup
    @3
    cort
    fvex
    fvmpt
    sylbir
end
