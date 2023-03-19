include "cfin3.mm"
include "wcel.mm"
include "com.mm"
include "cpw.mm"
include "wf.mm"
include "cv.mm"
include "csuc.mm"
include "cfv.mm"
include "wss.mm"
include "wral.mm"
include "w3a.mm"
include "crn.mm"
include "cint.mm"
include "cwdom.mm"
include "wbr.mm"
include "wn.mm"
include "isfin32i.mm"
include "3ad2ant1.mm"
include "wi.mm"
include "isf32lem11.mm"
include "3exp2.mm"
include "3imp.mm"
include "mt3d.mm"

theorem fin33i
  let vx: setvar x
  let cA: class A
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  let cV: class V

  disjoint A x
  disjoint F x
  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint b f
  disjoint b g
  disjoint b x
  disjoint b y
  disjoint A b
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
  disjoint V x
  assert |- ( ( A e. Fin3 /\ F : _om --> ~P A /\ A. x e. _om ( F ` suc x ) C_ ( F ` x ) ) -> |^| ran F e. ran F )

  proof
    cA
    cfin3
    wcel
    #
    com
    cA
    cpw
    cF
    wf
    #
    vx
    cv
    #
    csuc
    cF
    cfv
    @2
    cF
    cfv
    wss
    vx
    com
    wral
    #
    w3a
    cF
    crn
    #
    cint
    @4
    wcel
    #
    com
    cA
    cwdom
    wbr
    #
    @0
    @1
    @6
    wn
    @3
    cA
    isfin32i
    3ad2ant1
    @0
    @1
    @3
    @5
    wn
    #
    @6
    wi
    @0
    @1
    @3
    @7
    @6
    cF
    cA
    cfin3
    vx
    isf32lem11
    3exp2
    3imp
    mt3d
end
