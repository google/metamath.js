include "com.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wf1.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "ackbij1lem10.mm"
include "ackbij1lem16.mm"
include "rgen2a.mm"
include "dff13.mm"
include "mpbir2an.mm"

theorem ackbij1lem17
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cG: class G
  let cH: class H
  let cA: class A
  let cB: class B
  assume ackbij.f: |- F = ( x e. ( ~P _om i^i Fin ) |-> ( card ` U_ y e. x ( { y } X. ~P y ) ) )

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G x
  disjoint G y
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H x
  disjoint H y
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A x
  disjoint A y
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B x
  disjoint B y
  assert |- F : ( ~P _om i^i Fin ) -1-1-> _om

  proof
    com
    cpw
    cfn
    cin
    #
    com
    cF
    wf1
    @0
    com
    cF
    wf
    va
    cv
    #
    cF
    cfv
    vb
    cv
    #
    cF
    cfv
    wceq
    va
    vb
    weq
    wi
    #
    vb
    @0
    wral
    va
    @0
    wral
    vx
    vy
    cF
    ackbij.f
    ackbij1lem10
    @3
    va
    vb
    @0
    vx
    vy
    @1
    @2
    cF
    ackbij.f
    ackbij1lem16
    rgen2a
    va
    vb
    @0
    com
    cF
    dff13
    mpbir2an
end
