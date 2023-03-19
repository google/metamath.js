include "wfun.mm"
include "cuni.mm"
include "wss.mm"
include "ssid.mm"
include "frrlem5c.mm"
include "ax-mp.mm"
include "cfrecs.mm"
include "cv.mm"
include "wfn.mm"
include "cpred.mm"
include "wral.mm"
include "wa.mm"
include "cfv.mm"
include "cres.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "wex.mm"
include "cab.mm"
include "df-frecs.mm"
include "unieqi.mm"
include "3eqtr4i.mm"
include "funeqi.mm"
include "mpbir.mm"

theorem frrlem10
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let vf: setvar f
  let cF: class F
  let cG: class G
  assume frrlem10.1: |- R Fr A
  assume frrlem10.2: |- R Se A
  assume frrlem10.3: |- B = { f | E. x ( f Fn x /\ ( x C_ A /\ A. y e. x Pred ( R , A , y ) C_ x ) /\ A. y e. x ( f ` y ) = ( y G ( f |` Pred ( R , A , y ) ) ) ) }
  assume frrlem10.4: |- F = frecs ( R , A , G )

  disjoint A f
  disjoint A x
  disjoint A y
  disjoint f x
  disjoint f y
  disjoint x y
  disjoint F x
  disjoint G f
  disjoint G x
  disjoint G y
  disjoint R f
  disjoint R x
  disjoint R y
  disjoint B x
  assert |- Fun F

  proof
    cF
    wfun
    cB
    cuni
    #
    wfun
    #
    cB
    cB
    wss
    @1
    cB
    ssid
    vx
    vy
    cA
    cB
    cB
    cR
    vf
    cG
    frrlem10.1
    frrlem10.2
    frrlem10.3
    frrlem5c
    ax-mp
    cF
    @0
    cA
    cR
    cG
    cfrecs
    vf
    cv
    #
    vx
    cv
    #
    wfn
    @3
    cA
    wss
    cA
    cR
    vy
    cv
    #
    cpred
    #
    @3
    wss
    vy
    @3
    wral
    wa
    @4
    @2
    cfv
    @4
    @2
    @5
    cres
    cG
    co
    wceq
    vy
    @3
    wral
    w3a
    vx
    wex
    vf
    cab
    #
    cuni
    cF
    @0
    vx
    vy
    cA
    cR
    vf
    cG
    df-frecs
    frrlem10.4
    cB
    @6
    frrlem10.3
    unieqi
    3eqtr4i
    funeqi
    mpbir
end
