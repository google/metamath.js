include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cuni.mm"
include "wss.mm"
include "wa.mm"
include "com.mm"
include "wcel.mm"
include "cfv.mm"
include "csuc.mm"
include "wpss.mm"
include "wi.mm"
include "inf3lem1.mm"
include "a1i.mm"
include "inf3lem3.mm"
include "jcad.mm"
include "df-pss.mm"
include "syl6ibr.mm"

theorem inf3lem4
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
  assert |- ( ( x =/= (/) /\ x C_ U. x ) -> ( A e. _om -> ( F ` A ) C. ( F ` suc A ) ) )

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
    #
    cA
    com
    wcel
    #
    cA
    cF
    cfv
    #
    cA
    csuc
    cF
    cfv
    #
    wss
    #
    @3
    @4
    wne
    #
    wa
    @3
    @4
    wpss
    @1
    @2
    @5
    @6
    @2
    @5
    wi
    @1
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
    inf3lem1
    a1i
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
    inf3lem3
    jcad
    @3
    @4
    df-pss
    syl6ibr
end
