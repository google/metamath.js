include "wss.mm"
include "cuni.mm"
include "cdm.mm"
include "cv.mm"
include "ciun.mm"
include "dmuni.mm"
include "wral.mm"
include "wcel.mm"
include "ssel.mm"
include "frrlem3.mm"
include "syl6.mm"
include "ralrimiv.mm"
include "iunss.mm"
include "sylibr.mm"
include "syl5eqss.mm"

theorem frrlem5d
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vf: setvar f
  let cG: class G
  let vg: setvar g
  let vh: setvar h
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  let va: setvar a
  assume frrlem5.1: |- R Fr A
  assume frrlem5.2: |- R Se A
  assume frrlem5.3: |- B = { f | E. x ( f Fn x /\ ( x C_ A /\ A. y e. x Pred ( R , A , y ) C_ x ) /\ A. y e. x ( f ` y ) = ( y G ( f |` Pred ( R , A , y ) ) ) ) }

  disjoint A f
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint f x
  disjoint f y
  disjoint G f
  disjoint G x
  disjoint G y
  disjoint R f
  disjoint R x
  disjoint R y
  disjoint B x
  disjoint A g
  disjoint f g
  disjoint A h
  disjoint h x
  disjoint h y
  disjoint f h
  disjoint G h
  disjoint G g
  disjoint g u
  disjoint u v
  disjoint u x
  disjoint g v
  disjoint g x
  disjoint v x
  disjoint g y
  disjoint h u
  disjoint h v
  disjoint R g
  disjoint R h
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint f z
  disjoint G z
  disjoint R z
  disjoint x z
  disjoint y z
  disjoint C g
  disjoint B g
  disjoint B h
  disjoint B u
  disjoint B v
  disjoint g h
  disjoint A a
  disjoint a f
  disjoint a h
  disjoint a x
  disjoint a y
  disjoint a g
  disjoint B a
  disjoint G a
  disjoint R a
  assert |- ( C C_ B -> dom U. C C_ A )

  proof
    cC
    cB
    wss
    #
    cC
    cuni
    cdm
    vg
    cC
    vg
    cv
    #
    cdm
    #
    ciun
    #
    cA
    vg
    cC
    dmuni
    @0
    @2
    cA
    wss
    #
    vg
    cC
    wral
    @3
    cA
    wss
    @0
    @4
    vg
    cC
    @0
    @1
    cC
    wcel
    @1
    cB
    wcel
    @4
    cC
    cB
    @1
    ssel
    vx
    vy
    cA
    cB
    cR
    vf
    vg
    cG
    frrlem5.3
    frrlem3
    syl6
    ralrimiv
    vg
    cC
    @2
    cA
    iunss
    sylibr
    syl5eqss
end
