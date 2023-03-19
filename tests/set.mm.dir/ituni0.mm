include "wcel.mm"
include "c0.mm"
include "cfv.mm"
include "cvv.mm"
include "cv.mm"
include "cuni.mm"
include "cmpt.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "itunifval.mm"
include "fveq1d.mm"
include "fr0g.mm"
include "eqtrd.mm"

theorem ituni0
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cU: class U
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cB: class B
  let vd: setvar d
  assume ituni.u: |- U = ( x e. _V |-> ( rec ( ( y e. _V |-> U. y ) , x ) |` _om ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint a x
  disjoint b x
  disjoint c x
  disjoint a y
  disjoint b y
  disjoint c y
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint B x
  disjoint B y
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint d x
  disjoint d y
  disjoint a d
  disjoint b d
  disjoint c d
  disjoint U a
  disjoint U b
  disjoint U c
  disjoint U d
  assert |- ( A e. V -> ( ( U ` A ) ` (/) ) = A )

  proof
    cA
    cV
    wcel
    #
    c0
    cA
    cU
    cfv
    #
    cfv
    c0
    vy
    cvv
    vy
    cv
    cuni
    cmpt
    #
    cA
    crdg
    com
    cres
    #
    cfv
    cA
    @0
    c0
    @1
    @3
    vx
    vy
    cA
    cU
    cV
    ituni.u
    itunifval
    fveq1d
    cA
    cV
    @2
    fr0g
    eqtrd
end
