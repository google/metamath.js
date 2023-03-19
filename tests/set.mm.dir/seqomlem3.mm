include "c0.mm"
include "com.mm"
include "cima.mm"
include "cfv.mm"
include "cid.mm"
include "wceq.mm"
include "wbr.mm"
include "cop.mm"
include "wcel.mm"
include "cres.mm"
include "crn.mm"
include "cvv.mm"
include "cv.mm"
include "csuc.mm"
include "co.mm"
include "cmpt2.mm"
include "crdg.mm"
include "peano1.mm"
include "fvres.mm"
include "ax-mp.mm"
include "fveq1i.mm"
include "opex.mm"
include "rdg0.mm"
include "3eqtri.mm"
include "wfn.mm"
include "frfnom.mm"
include "reseq1i.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "fnfvelrn.mm"
include "mp2an.mm"
include "eqeltrri.mm"
include "df-ima.mm"
include "eleqtrri.mm"
include "df-br.mm"
include "wb.mm"
include "seqomlem2.mm"
include "fnbrfvb.mm"

theorem seqomlem3
  let vv: setvar v
  let cQ: class Q
  let vi: setvar i
  let cF: class F
  let cI: class I
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cA: class A
  assume seqomlem.a: |- Q = rec ( ( i e. _om , v e. _V |-> <. suc i , ( i F v ) >. ) , <. (/) , ( _I ` I ) >. )

  disjoint Q i
  disjoint Q v
  disjoint i v
  disjoint F i
  disjoint F v
  disjoint Q a
  disjoint Q b
  disjoint Q c
  disjoint a b
  disjoint a c
  disjoint a i
  disjoint a v
  disjoint b c
  disjoint b i
  disjoint b v
  disjoint c i
  disjoint c v
  disjoint A a
  disjoint A b
  disjoint A i
  disjoint A v
  disjoint F a
  disjoint F b
  disjoint I a
  disjoint I b
  assert |- ( ( Q " _om ) ` (/) ) = ( _I ` I )

  proof
    c0
    cQ
    com
    cima
    #
    cfv
    cI
    cid
    cfv
    #
    wceq
    #
    c0
    @1
    @0
    wbr
    #
    @3
    c0
    @1
    cop
    #
    @0
    wcel
    @4
    cQ
    com
    cres
    #
    crn
    #
    @0
    c0
    @5
    cfv
    #
    @4
    @6
    @7
    c0
    cQ
    cfv
    #
    c0
    vi
    vv
    com
    cvv
    vi
    cv
    #
    csuc
    @9
    vv
    cv
    cF
    co
    cop
    cmpt2
    #
    @4
    crdg
    #
    cfv
    @4
    c0
    com
    wcel
    #
    @7
    @8
    wceq
    peano1
    c0
    com
    cQ
    fvres
    ax-mp
    c0
    cQ
    @11
    seqomlem.a
    fveq1i
    @4
    @10
    c0
    @1
    opex
    rdg0
    3eqtri
    @5
    com
    wfn
    #
    @12
    @7
    @6
    wcel
    @13
    @11
    com
    cres
    #
    com
    wfn
    @4
    @10
    frfnom
    com
    @5
    @14
    cQ
    @11
    com
    seqomlem.a
    reseq1i
    fneq1i
    mpbir
    peano1
    com
    c0
    @5
    fnfvelrn
    mp2an
    eqeltrri
    cQ
    com
    df-ima
    eleqtrri
    c0
    @1
    @0
    df-br
    mpbir
    @0
    com
    wfn
    @12
    @2
    @3
    wb
    vv
    cQ
    vi
    cF
    cI
    seqomlem.a
    seqomlem2
    peano1
    com
    c0
    @1
    @0
    fnbrfvb
    mp2an
    mpbir
end
