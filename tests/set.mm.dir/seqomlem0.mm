include "com.mm"
include "cvv.mm"
include "cv.mm"
include "csuc.mm"
include "co.mm"
include "cop.mm"
include "cmpt2.mm"
include "wceq.mm"
include "c0.mm"
include "cid.mm"
include "cfv.mm"
include "crdg.mm"
include "weq.mm"
include "suceq.mm"
include "oveq1.mm"
include "opeq12d.mm"
include "oveq2.mm"
include "opeq2d.mm"
include "cbvmpt2v.mm"
include "rdgeq1.mm"
include "ax-mp.mm"

theorem seqomlem0
  let cF: class F
  let cI: class I
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d

  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint b c
  disjoint b d
  disjoint c d
  disjoint I a
  disjoint I b
  disjoint I c
  disjoint I d
  assert |- rec ( ( a e. _om , b e. _V |-> <. suc a , ( a F b ) >. ) , <. (/) , ( _I ` I ) >. ) = rec ( ( c e. _om , d e. _V |-> <. suc c , ( c F d ) >. ) , <. (/) , ( _I ` I ) >. )

  proof
    va
    vb
    com
    cvv
    va
    cv
    #
    csuc
    #
    @0
    vb
    cv
    #
    cF
    co
    #
    cop
    #
    cmpt2
    #
    vc
    vd
    com
    cvv
    vc
    cv
    #
    csuc
    #
    @6
    vd
    cv
    #
    cF
    co
    #
    cop
    #
    cmpt2
    #
    wceq
    @5
    c0
    cI
    cid
    cfv
    cop
    #
    crdg
    @11
    @12
    crdg
    wceq
    va
    vb
    vc
    vd
    com
    cvv
    @4
    @10
    @7
    @6
    @2
    cF
    co
    #
    cop
    va
    vc
    weq
    @1
    @7
    @3
    @13
    @0
    @6
    suceq
    @0
    @6
    @2
    cF
    oveq1
    opeq12d
    vb
    vd
    weq
    @13
    @9
    @7
    @2
    @8
    @6
    cF
    oveq2
    opeq2d
    cbvmpt2v
    @12
    @5
    @11
    rdgeq1
    ax-mp
end
