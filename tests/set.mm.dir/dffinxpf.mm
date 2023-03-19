include "cfinxp.mm"
include "com.mm"
include "wcel.mm"
include "c0.mm"
include "cvv.mm"
include "cv.mm"
include "c1o.mm"
include "wceq.mm"
include "wa.mm"
include "cxp.mm"
include "cuni.mm"
include "c1st.mm"
include "cfv.mm"
include "cop.mm"
include "cif.mm"
include "cmpt2.mm"
include "crdg.mm"
include "cab.mm"
include "df-finxp.mm"
include "rdgeq1.mm"
include "ax-mp.mm"
include "fveq1i.mm"
include "eqeq2i.mm"
include "anbi2i.mm"
include "abbii.mm"
include "eqtr4i.mm"

theorem dffinxpf
  let vx: setvar x
  let vy: setvar y
  let cU: class U
  let vn: setvar n
  let cF: class F
  let cN: class N
  assume dffinxpf.1: |- F = ( n e. _om , x e. _V |-> if ( ( n = 1o /\ x e. U ) , (/) , if ( x e. ( _V X. U ) , <. U. n , ( 1st ` x ) >. , <. n , x >. ) ) )

  disjoint U n
  disjoint U x
  disjoint U y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint N n
  disjoint N x
  disjoint N y
  assert |- ( U ^^ N ) = { y | ( N e. _om /\ (/) = ( rec ( F , <. N , y >. ) ` N ) ) }

  proof
    cU
    cN
    cfinxp
    cN
    com
    wcel
    #
    c0
    cN
    vn
    vx
    com
    cvv
    vn
    cv
    #
    c1o
    wceq
    vx
    cv
    #
    cU
    wcel
    wa
    c0
    @2
    cvv
    cU
    cxp
    wcel
    @1
    cuni
    @2
    c1st
    cfv
    cop
    @1
    @2
    cop
    cif
    cif
    cmpt2
    #
    cN
    vy
    cv
    cop
    #
    crdg
    #
    cfv
    #
    wceq
    #
    wa
    #
    vy
    cab
    @0
    c0
    cN
    cF
    @4
    crdg
    #
    cfv
    #
    wceq
    #
    wa
    #
    vy
    cab
    vx
    vy
    cU
    vn
    cN
    df-finxp
    @12
    @8
    vy
    @11
    @7
    @0
    @10
    @6
    c0
    cN
    @9
    @5
    cF
    @3
    wceq
    @9
    @5
    wceq
    dffinxpf.1
    @4
    cF
    @3
    rdgeq1
    ax-mp
    fveq1i
    eqeq2i
    anbi2i
    abbii
    eqtr4i
end
