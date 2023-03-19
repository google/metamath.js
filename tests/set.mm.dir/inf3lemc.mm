include "com.mm"
include "wcel.mm"
include "csuc.mm"
include "c0.mm"
include "crdg.mm"
include "cres.mm"
include "cfv.mm"
include "frsuc.mm"
include "fveq1i.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"

theorem inf3lemc
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
  assert |- ( A e. _om -> ( F ` suc A ) = ( G ` ( F ` A ) ) )

  proof
    cA
    com
    wcel
    cA
    csuc
    #
    cG
    c0
    crdg
    com
    cres
    #
    cfv
    cA
    @1
    cfv
    #
    cG
    cfv
    @0
    cF
    cfv
    cA
    cF
    cfv
    #
    cG
    cfv
    c0
    cA
    cG
    frsuc
    @0
    cF
    @1
    inf3lem.2
    fveq1i
    @3
    @2
    cG
    cA
    cF
    @1
    inf3lem.2
    fveq1i
    fveq2i
    3eqtr4g
end
