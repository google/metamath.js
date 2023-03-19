include "crecs.mm"
include "cdm.mm"
include "con0.mm"
include "wcel.mm"
include "wceq.mm"
include "cvv.mm"
include "tfrlem13.mm"
include "wfun.mm"
include "tfrlem7.mm"
include "funex.mm"
include "mpan.mm"
include "mto.mm"
include "word.mm"
include "wo.mm"
include "tfrlem8.mm"
include "ordeleqon.mm"
include "mpbi.mm"
include "mtpor.mm"

theorem tfrlem14
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let cF: class F
  let vg: setvar g
  let vz: setvar z
  let cB: class B
  let cC: class C
  let va: setvar a
  let vh: setvar h
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume tfrlem.1: |- A = { f | E. x e. On ( f Fn x /\ A. y e. x ( f ` y ) = ( F ` ( f |` y ) ) ) }

  disjoint f x
  disjoint f y
  disjoint x y
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint f g
  disjoint f z
  disjoint B f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint B g
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C f
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint f h
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint g h
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint F g
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint F h
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint F z
  disjoint A g
  disjoint A h
  disjoint A z
  assert |- dom recs ( F ) = On

  proof
    cF
    crecs
    #
    cdm
    #
    con0
    wcel
    #
    @1
    con0
    wceq
    #
    @2
    @0
    cvv
    wcel
    #
    vx
    vy
    cA
    vf
    cF
    tfrlem.1
    tfrlem13
    @0
    wfun
    @2
    @4
    vx
    vy
    cA
    vf
    cF
    tfrlem.1
    tfrlem7
    con0
    @0
    funex
    mpan
    mto
    @1
    word
    @2
    @3
    wo
    vx
    vy
    cA
    vf
    cF
    tfrlem.1
    tfrlem8
    @1
    ordeleqon
    mpbi
    mtpor
end
