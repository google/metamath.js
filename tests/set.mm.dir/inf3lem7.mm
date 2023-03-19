include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cuni.mm"
include "wss.mm"
include "wa.mm"
include "com.mm"
include "cpw.mm"
include "wf1.mm"
include "cvv.mm"
include "wcel.mm"
include "inf3lem6.mm"
include "vpwex.mm"
include "f1dmex.mm"
include "sylancl.mm"

theorem inf3lem7
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  assume inf3lem.1: |- G = ( y e. _V |-> { w e. x | ( w i^i x ) C_ y } )
  assume inf3lem.2: |- F = ( rec ( G , (/) ) |` _om )
  assume inf3lem.3: |- A e. _V
  assume inf3lem.4: |- B e. _V

  disjoint x y
  disjoint w x
  disjoint w y
  disjoint v x
  disjoint u x
  disjoint f x
  disjoint v y
  disjoint u y
  disjoint f y
  disjoint v w
  disjoint u w
  disjoint f w
  disjoint u v
  disjoint f v
  disjoint f u
  disjoint G v
  disjoint G u
  disjoint G f
  disjoint F v
  disjoint F u
  disjoint F f
  disjoint A v
  disjoint A u
  disjoint A f
  disjoint B v
  disjoint B u
  disjoint B f
  assert |- ( ( x =/= (/) /\ x C_ U. x ) -> _om e. _V )

  proof
    vx
    cv
    #
    c0
    wne
    @0
    @0
    cuni
    wss
    wa
    com
    @0
    cpw
    #
    cF
    wf1
    @1
    cvv
    wcel
    com
    cvv
    wcel
    vx
    vy
    vw
    cA
    cB
    cF
    cG
    inf3lem.1
    inf3lem.2
    inf3lem.3
    inf3lem.4
    inf3lem6
    vx
    vpwex
    com
    @1
    cvv
    cF
    f1dmex
    sylancl
end
