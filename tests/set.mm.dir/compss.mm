include "ccnv.mm"
include "cima.mm"
include "cv.mm"
include "cdif.mm"
include "wcel.mm"
include "cpw.mm"
include "crab.mm"
include "compsscnv.mm"
include "imaeq1i.mm"
include "cmpt.mm"
include "difeq2.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "mptpreima.mm"
include "eqtr3i.mm"

theorem compss
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let cV: class V
  let cX: class X
  assume compss.a: |- F = ( x e. ~P A |-> ( A \ x ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F y
  disjoint G y
  disjoint a b
  disjoint a c
  disjoint a f
  disjoint a g
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint b c
  disjoint b f
  disjoint b g
  disjoint b x
  disjoint b y
  disjoint A b
  disjoint c f
  disjoint c g
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint F a
  disjoint F b
  disjoint F f
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint V x
  disjoint V y
  disjoint X a
  disjoint X b
  disjoint X c
  assert |- ( F " G ) = { y e. ~P A | ( A \ y ) e. G }

  proof
    cF
    ccnv
    #
    cG
    cima
    cF
    cG
    cima
    cA
    vy
    cv
    #
    cdif
    #
    cG
    wcel
    vy
    cA
    cpw
    #
    crab
    @0
    cF
    cG
    vx
    cA
    cF
    compss.a
    compsscnv
    imaeq1i
    vy
    @3
    @2
    cG
    cF
    cF
    vx
    @3
    cA
    vx
    cv
    #
    cdif
    #
    cmpt
    vy
    @3
    @2
    cmpt
    compss.a
    vx
    vy
    @3
    @5
    @2
    @4
    @1
    cA
    difeq2
    cbvmptv
    eqtri
    mptpreima
    eqtr3i
end
