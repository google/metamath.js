include "con0.mm"
include "cv.mm"
include "csuc.mm"
include "cmpt.mm"
include "com.mm"
include "c2o.mm"
include "comu.mm"
include "co.mm"
include "eqid.mm"
include "fin1a2lem7.mm"

theorem fin1a2lem8
  let vx: setvar x
  let cA: class A
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vy: setvar y
  let cB: class B
  let cX: class X
  let cC: class C

  disjoint A x
  disjoint V x
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b x
  disjoint b y
  disjoint A b
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint d h
  disjoint d x
  disjoint d y
  disjoint A d
  disjoint e f
  disjoint e g
  disjoint e h
  disjoint e x
  disjoint e y
  disjoint A e
  disjoint f g
  disjoint f h
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint g h
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint h x
  disjoint h y
  disjoint A h
  disjoint x y
  disjoint A y
  disjoint B d
  disjoint B e
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint V c
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint C e
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint C x
  assert |- ( ( A e. V /\ A. x e. ~P A ( x e. Fin3 \/ ( A \ x ) e. Fin3 ) ) -> A e. Fin3 )

  proof
    vy
    vx
    cA
    vy
    con0
    vy
    cv
    #
    csuc
    cmpt
    #
    vy
    com
    c2o
    @0
    comu
    co
    cmpt
    #
    cV
    @2
    eqid
    @1
    eqid
    fin1a2lem7
end
