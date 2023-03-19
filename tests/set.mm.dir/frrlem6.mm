include "wrel.mm"
include "cuni.mm"
include "cv.mm"
include "reluni.mm"
include "wcel.mm"
include "wfun.mm"
include "frrlem2.mm"
include "funrel.mm"
include "syl.mm"
include "mprgbir.mm"
include "wfn.mm"
include "wss.mm"
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
include "cfrecs.mm"
include "df-frecs.mm"
include "eqtri.mm"
include "unieqi.mm"
include "eqtr4i.mm"
include "releqi.mm"
include "mpbir.mm"

theorem frrlem6
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let vf: setvar f
  let cF: class F
  let cG: class G
  let vg: setvar g
  assume frrlem6.1: |- B = { f | E. x ( f Fn x /\ ( x C_ A /\ A. y e. x Pred ( R , A , y ) C_ x ) /\ A. y e. x ( f ` y ) = ( y G ( f |` Pred ( R , A , y ) ) ) ) }
  assume frrlem6.2: |- F = frecs ( R , A , G )

  disjoint A f
  disjoint A x
  disjoint A y
  disjoint f x
  disjoint f y
  disjoint x y
  disjoint G f
  disjoint G x
  disjoint G y
  disjoint R f
  disjoint R x
  disjoint R y
  disjoint A g
  disjoint f g
  disjoint g x
  disjoint g y
  disjoint G g
  disjoint R g
  disjoint B g
  assert |- Rel F

  proof
    cF
    wrel
    cB
    cuni
    #
    wrel
    #
    @1
    vg
    cv
    #
    wrel
    #
    vg
    cB
    vg
    cB
    reluni
    @2
    cB
    wcel
    @2
    wfun
    @3
    vx
    vy
    cA
    cB
    cR
    vf
    vg
    cG
    frrlem6.1
    frrlem2
    @2
    funrel
    syl
    mprgbir
    cF
    @0
    cF
    vf
    cv
    #
    vx
    cv
    #
    wfn
    @5
    cA
    wss
    cA
    cR
    vy
    cv
    #
    cpred
    #
    @5
    wss
    vy
    @5
    wral
    wa
    @6
    @4
    cfv
    @6
    @4
    @7
    cres
    cG
    co
    wceq
    vy
    @5
    wral
    w3a
    vx
    wex
    vf
    cab
    #
    cuni
    #
    @0
    cF
    cA
    cR
    cG
    cfrecs
    @9
    frrlem6.2
    vx
    vy
    cA
    cR
    vf
    cG
    df-frecs
    eqtri
    cB
    @8
    frrlem6.1
    unieqi
    eqtr4i
    releqi
    mpbir
end
