include "cnp.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "genpv.mm"
include "eleq2d.mm"
include "cvv.mm"
include "id.mm"
include "ovex.mm"
include "syl6eqel.mm"
include "rexlimivw.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "elab3.mm"
include "syl6bb.mm"

theorem genpelv
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let vg: setvar g
  let vh: setvar h
  let cF: class F
  let cG: class G
  let vf: setvar f
  let cD: class D
  assume genp.1: |- F = ( w e. P. , v e. P. |-> { x | E. y e. w E. z e. v x = ( y G z ) } )
  assume genp.2: |- ( ( y e. Q. /\ z e. Q. ) -> ( y G z ) e. Q. )

  disjoint x y
  disjoint x z
  disjoint g x
  disjoint h x
  disjoint A x
  disjoint y z
  disjoint g y
  disjoint h y
  disjoint A y
  disjoint g z
  disjoint h z
  disjoint A z
  disjoint g h
  disjoint A g
  disjoint A h
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B g
  disjoint B h
  disjoint w x
  disjoint v x
  disjoint G x
  disjoint w y
  disjoint v y
  disjoint G y
  disjoint w z
  disjoint v z
  disjoint G z
  disjoint v w
  disjoint g w
  disjoint h w
  disjoint G w
  disjoint g v
  disjoint h v
  disjoint G v
  disjoint G g
  disjoint G h
  disjoint F g
  disjoint C g
  disjoint C h
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint f g
  disjoint f h
  disjoint A f
  disjoint B f
  disjoint f w
  disjoint f v
  disjoint G f
  disjoint F f
  disjoint C f
  disjoint D g
  disjoint D h
  assert |- ( ( A e. P. /\ B e. P. ) -> ( C e. ( A F B ) <-> E. g e. A E. h e. B C = ( g G h ) ) )

  proof
    cA
    cnp
    wcel
    cB
    cnp
    wcel
    wa
    #
    cC
    cA
    cB
    cF
    co
    #
    wcel
    cC
    vf
    cv
    #
    vg
    cv
    #
    vh
    cv
    #
    cG
    co
    #
    wceq
    #
    vh
    cB
    wrex
    vg
    cA
    wrex
    #
    vf
    cab
    #
    wcel
    cC
    @5
    wceq
    #
    vh
    cB
    wrex
    #
    vg
    cA
    wrex
    #
    @0
    @1
    @8
    cC
    vx
    vy
    vz
    vw
    vv
    cA
    cB
    vf
    vg
    vh
    cF
    cG
    genp.1
    genp.2
    genpv
    eleq2d
    @7
    @11
    vf
    cC
    @10
    cC
    cvv
    wcel
    #
    vg
    cA
    @9
    @12
    vh
    cB
    @9
    cC
    @5
    cvv
    @9
    id
    @3
    @4
    cG
    ovex
    syl6eqel
    rexlimivw
    rexlimivw
    @2
    cC
    wceq
    @6
    @9
    vg
    vh
    cA
    cB
    @2
    cC
    @5
    eqeq1
    2rexbidv
    elab3
    syl6bb
end
