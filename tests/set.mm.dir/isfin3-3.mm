include "cfin3.mm"
include "isf33lem.mm"
include "isfin3ds.mm"

theorem isfin3-3
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vy: setvar y
  let cF: class F

  disjoint f x
  disjoint A f
  disjoint A x
  disjoint V x
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
  disjoint f y
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint x y
  disjoint A y
  disjoint F a
  disjoint F b
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint V a
  disjoint V b
  assert |- ( A e. V -> ( A e. Fin3 <-> A. f e. ( ~P A ^m _om ) ( A. x e. _om ( f ` suc x ) C_ ( f ` x ) -> |^| ran f e. ran f ) ) )

  proof
    vx
    cA
    vf
    vg
    cfin3
    cV
    va
    vb
    vb
    vg
    va
    isf33lem
    isfin3ds
end
