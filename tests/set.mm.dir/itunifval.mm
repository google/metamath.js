include "wcel.mm"
include "cvv.mm"
include "cfv.mm"
include "cv.mm"
include "cuni.mm"
include "cmpt.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "wceq.mm"
include "elex.mm"
include "rdgeq2.mm"
include "reseq1d.mm"
include "wfun.mm"
include "rdgfun.mm"
include "omex.mm"
include "resfunexg.mm"
include "mp2an.mm"
include "fvmpt.mm"
include "syl.mm"

theorem itunifval
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
  assert |- ( A e. V -> ( U ` A ) = ( rec ( ( y e. _V |-> U. y ) , A ) |` _om ) )

  proof
    cA
    cV
    wcel
    cA
    cvv
    wcel
    cA
    cU
    cfv
    vy
    cvv
    vy
    cv
    cuni
    cmpt
    #
    cA
    crdg
    #
    com
    cres
    #
    wceq
    cA
    cV
    elex
    vx
    cA
    @0
    vx
    cv
    #
    crdg
    #
    com
    cres
    @2
    cvv
    cU
    @3
    cA
    wceq
    @4
    @1
    com
    @3
    cA
    @0
    rdgeq2
    reseq1d
    ituni.u
    @1
    wfun
    com
    cvv
    wcel
    @2
    cvv
    wcel
    cA
    @0
    rdgfun
    omex
    @1
    com
    cvv
    resfunexg
    mp2an
    fvmpt
    syl
end
