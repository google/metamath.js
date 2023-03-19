include "cdm.mm"
include "cv.mm"
include "ciun.mm"
include "cuni.mm"
include "cfrecs.mm"
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
include "df-frecs.mm"
include "unieqi.mm"
include "3eqtr4i.mm"
include "dmeqi.mm"
include "dmuni.mm"
include "eqtri.mm"
include "iunss.mm"
include "frrlem3.mm"
include "mprgbir.mm"
include "eqsstri.mm"

theorem frrlem7
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
  assert |- dom F C_ A

  proof
    cF
    cdm
    #
    vg
    cB
    vg
    cv
    cdm
    #
    ciun
    #
    cA
    @0
    cB
    cuni
    #
    cdm
    @2
    cF
    @3
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
    cF
    @3
    vx
    vy
    cA
    cR
    vf
    cG
    df-frecs
    frrlem6.2
    cB
    @8
    frrlem6.1
    unieqi
    3eqtr4i
    dmeqi
    vg
    cB
    dmuni
    eqtri
    @2
    cA
    wss
    @1
    cA
    wss
    vg
    cB
    vg
    cB
    @1
    cA
    iunss
    vx
    vy
    cA
    cB
    cR
    vf
    vg
    cG
    frrlem6.1
    frrlem3
    mprgbir
    eqsstri
end
