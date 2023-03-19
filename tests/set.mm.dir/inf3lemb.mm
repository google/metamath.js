include "c0.mm"
include "cfv.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "fveq1i.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "0ex.mm"
include "fr0g.mm"
include "ax-mp.mm"
include "eqtri.mm"

theorem inf3lemb
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
  assert |- ( F ` (/) ) = (/)

  proof
    c0
    cF
    cfv
    c0
    cG
    c0
    crdg
    com
    cres
    #
    cfv
    #
    c0
    c0
    cF
    @0
    inf3lem.2
    fveq1i
    c0
    cvv
    wcel
    @1
    c0
    wceq
    0ex
    c0
    cvv
    cG
    fr0g
    ax-mp
    eqtri
end
