include "com.mm"
include "wcel.mm"
include "csuc.mm"
include "cima.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wbr.mm"
include "cop.mm"
include "cres.mm"
include "crn.mm"
include "peano2.mm"
include "fvres.mm"
include "syl.mm"
include "cvv.mm"
include "cv.mm"
include "cmpt2.mm"
include "c2nd.mm"
include "c0.mm"
include "cid.mm"
include "crdg.mm"
include "frsuc.mm"
include "fveq1i.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "3eqtr3d.mm"
include "seqomlem1.mm"
include "df-ov.mm"
include "fvex.mm"
include "suceq.mm"
include "oveq1.mm"
include "opeq12d.mm"
include "oveq2.mm"
include "opeq2d.mm"
include "eqid.mm"
include "opex.mm"
include "ovmpt2.mm"
include "mpan2.mm"
include "eqtrd.mm"
include "wfn.mm"
include "frfnom.mm"
include "reseq1i.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "fnfvelrn.mm"
include "mpan.mm"
include "eqeltrrd.mm"
include "df-ima.mm"
include "syl6eleqr.mm"
include "df-br.mm"
include "sylibr.mm"
include "wb.mm"
include "seqomlem2.mm"
include "fnbrfvb.mm"
include "mpbird.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "syl5eqr.mm"
include "3eqtrd.mm"
include "sylancr.mm"

theorem seqomlem4
  let vv: setvar v
  let cA: class A
  let cQ: class Q
  let vi: setvar i
  let cF: class F
  let cI: class I
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume seqomlem.a: |- Q = rec ( ( i e. _om , v e. _V |-> <. suc i , ( i F v ) >. ) , <. (/) , ( _I ` I ) >. )

  disjoint Q i
  disjoint Q v
  disjoint i v
  disjoint A i
  disjoint A v
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
  disjoint F a
  disjoint F b
  disjoint I a
  disjoint I b
  assert |- ( A e. _om -> ( ( Q " _om ) ` suc A ) = ( A F ( ( Q " _om ) ` A ) ) )

  proof
    cA
    com
    wcel
    #
    cA
    csuc
    #
    cQ
    com
    cima
    #
    cfv
    cA
    cA
    @2
    cfv
    #
    cF
    co
    #
    wceq
    #
    @1
    @4
    @2
    wbr
    #
    @0
    @1
    @4
    cop
    #
    @2
    wcel
    @6
    @0
    @7
    cQ
    com
    cres
    #
    crn
    #
    @2
    @0
    @1
    @8
    cfv
    #
    @7
    @9
    @0
    @10
    @1
    cQ
    cfv
    #
    @7
    @0
    @1
    com
    wcel
    #
    @10
    @11
    wceq
    cA
    peano2
    #
    @1
    com
    cQ
    fvres
    syl
    @0
    @11
    cA
    cQ
    cfv
    #
    vi
    vv
    com
    cvv
    vi
    cv
    #
    csuc
    #
    @15
    vv
    cv
    #
    cF
    co
    #
    cop
    #
    cmpt2
    #
    cfv
    #
    cA
    @14
    c2nd
    cfv
    #
    cop
    #
    @20
    cfv
    #
    @7
    @0
    @1
    @20
    c0
    cI
    cid
    cfv
    cop
    #
    crdg
    #
    com
    cres
    #
    cfv
    #
    cA
    @27
    cfv
    #
    @20
    cfv
    @11
    @21
    @25
    cA
    @20
    frsuc
    @0
    @28
    @1
    @26
    cfv
    #
    @11
    @0
    @12
    @28
    @30
    wceq
    @13
    @1
    com
    @26
    fvres
    syl
    @1
    cQ
    @26
    seqomlem.a
    fveq1i
    syl6eqr
    @0
    @29
    @14
    @20
    @0
    @29
    cA
    @26
    cfv
    @14
    cA
    com
    @26
    fvres
    cA
    cQ
    @26
    seqomlem.a
    fveq1i
    syl6eqr
    fveq2d
    3eqtr3d
    @0
    @14
    @23
    @20
    vv
    cA
    cQ
    vi
    cF
    cI
    seqomlem.a
    seqomlem1
    #
    fveq2d
    @0
    @24
    cA
    @22
    @20
    co
    #
    @7
    cA
    @22
    @20
    df-ov
    @0
    @32
    @1
    cA
    @22
    cF
    co
    #
    cop
    #
    @7
    @0
    @22
    cvv
    wcel
    @32
    @34
    wceq
    @14
    c2nd
    fvex
    vi
    vv
    cA
    @22
    com
    cvv
    @19
    @34
    @20
    @1
    cA
    @17
    cF
    co
    #
    cop
    @15
    cA
    wceq
    @16
    @1
    @18
    @35
    @15
    cA
    suceq
    @15
    cA
    @17
    cF
    oveq1
    opeq12d
    @17
    @22
    wceq
    @35
    @33
    @1
    @17
    @22
    cA
    cF
    oveq2
    opeq2d
    @20
    eqid
    @1
    @33
    opex
    ovmpt2
    mpan2
    @0
    @33
    @4
    @1
    @0
    @22
    @3
    cA
    cF
    @0
    @3
    @22
    @0
    @3
    @22
    wceq
    #
    cA
    @22
    @2
    wbr
    #
    @0
    @23
    @2
    wcel
    @37
    @0
    @23
    @9
    @2
    @0
    cA
    @8
    cfv
    #
    @23
    @9
    @0
    @38
    @14
    @23
    cA
    com
    cQ
    fvres
    @31
    eqtrd
    @8
    com
    wfn
    #
    @0
    @38
    @9
    wcel
    @39
    @27
    com
    wfn
    @25
    @20
    frfnom
    com
    @8
    @27
    cQ
    @26
    com
    seqomlem.a
    reseq1i
    fneq1i
    mpbir
    #
    com
    cA
    @8
    fnfvelrn
    mpan
    eqeltrrd
    cQ
    com
    df-ima
    #
    syl6eleqr
    cA
    @22
    @2
    df-br
    sylibr
    @2
    com
    wfn
    #
    @0
    @36
    @37
    wb
    vv
    cQ
    vi
    cF
    cI
    seqomlem.a
    seqomlem2
    #
    com
    cA
    @22
    @2
    fnbrfvb
    mpan
    mpbird
    eqcomd
    oveq2d
    opeq2d
    eqtrd
    syl5eqr
    3eqtrd
    eqtrd
    @0
    @39
    @12
    @10
    @9
    wcel
    @40
    @13
    com
    @1
    @8
    fnfvelrn
    sylancr
    eqeltrrd
    @41
    syl6eleqr
    @1
    @4
    @2
    df-br
    sylibr
    @0
    @42
    @12
    @5
    @6
    wb
    @43
    @13
    com
    @1
    @4
    @2
    fnbrfvb
    sylancr
    mpbird
end
