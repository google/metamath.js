include "wcel.mm"
include "cpw.mm"
include "cv.mm"
include "cdif.mm"
include "wss.mm"
include "difss.mm"
include "elpw2g.mm"
include "mpbiri.mm"
include "adantr.mm"
include "fmptd.mm"

theorem isf34lem2
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  let cX: class X
  let cG: class G
  assume compss.a: |- F = ( x e. ~P A |-> ( A \ x ) )

  disjoint A x
  disjoint V x
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
  disjoint x y
  disjoint A y
  disjoint F a
  disjoint F b
  disjoint F f
  disjoint F y
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint V y
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint G y
  assert |- ( A e. V -> F : ~P A --> ~P A )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    cpw
    #
    cA
    vx
    cv
    #
    cdif
    #
    @1
    cF
    @0
    @3
    @1
    wcel
    #
    @2
    @1
    wcel
    @0
    @4
    @3
    cA
    wss
    cA
    @2
    difss
    @3
    cA
    cV
    elpw2g
    mpbiri
    adantr
    compss.a
    fmptd
end
