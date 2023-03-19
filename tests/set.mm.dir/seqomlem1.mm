include "cv.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "wceq.mm"
include "c0.mm"
include "csuc.mm"
include "fveq2.mm"
include "id.mm"
include "fveq2d.mm"
include "opeq12d.mm"
include "eqeq12d.mm"
include "cid.mm"
include "com.mm"
include "cvv.mm"
include "co.mm"
include "cmpt2.mm"
include "crdg.mm"
include "fveq1i.mm"
include "opex.mm"
include "rdg0.mm"
include "eqtri.mm"
include "0ex.mm"
include "fvex.mm"
include "op2nd.mm"
include "eqcomi.mm"
include "opeq2i.mm"
include "opeq2d.mm"
include "3eqtr4a.mm"
include "ax-mp.mm"
include "wcel.mm"
include "df-ov.mm"
include "suceq.mm"
include "oveq1.mm"
include "oveq2.mm"
include "eqid.mm"
include "ovmpt2.mm"
include "mpan2.mm"
include "syl5eqr.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "vex.mm"
include "sucex.mm"
include "ovex.mm"
include "a1i.mm"
include "syld.mm"
include "cres.mm"
include "frsuc.mm"
include "peano2.mm"
include "fvres.mm"
include "syl.mm"
include "syl6eqr.mm"
include "3eqtr3d.mm"
include "sylibrd.mm"
include "finds.mm"

theorem seqomlem1
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
  assert |- ( A e. _om -> ( Q ` A ) = <. A , ( 2nd ` ( Q ` A ) ) >. )

  proof
    va
    cv
    #
    cQ
    cfv
    #
    @0
    @1
    c2nd
    cfv
    #
    cop
    #
    wceq
    c0
    cQ
    cfv
    #
    c0
    @4
    c2nd
    cfv
    #
    cop
    #
    wceq
    #
    vb
    cv
    #
    cQ
    cfv
    #
    @8
    @9
    c2nd
    cfv
    #
    cop
    #
    wceq
    #
    @8
    csuc
    #
    cQ
    cfv
    #
    @13
    @14
    c2nd
    cfv
    #
    cop
    #
    wceq
    #
    cA
    cQ
    cfv
    #
    cA
    @18
    c2nd
    cfv
    #
    cop
    #
    wceq
    va
    vb
    cA
    @0
    c0
    wceq
    #
    @1
    @4
    @3
    @6
    @0
    c0
    cQ
    fveq2
    #
    @21
    @0
    c0
    @2
    @5
    @21
    id
    @21
    @1
    @4
    c2nd
    @22
    fveq2d
    opeq12d
    eqeq12d
    @0
    @8
    wceq
    #
    @1
    @9
    @3
    @11
    @0
    @8
    cQ
    fveq2
    #
    @23
    @0
    @8
    @2
    @10
    @23
    id
    @23
    @1
    @9
    c2nd
    @24
    fveq2d
    opeq12d
    eqeq12d
    @0
    @13
    wceq
    #
    @1
    @14
    @3
    @16
    @0
    @13
    cQ
    fveq2
    #
    @25
    @0
    @13
    @2
    @15
    @25
    id
    @25
    @1
    @14
    c2nd
    @26
    fveq2d
    opeq12d
    eqeq12d
    @0
    cA
    wceq
    #
    @1
    @18
    @3
    @20
    @0
    cA
    cQ
    fveq2
    #
    @27
    @0
    cA
    @2
    @19
    @27
    id
    @27
    @1
    @18
    c2nd
    @28
    fveq2d
    opeq12d
    eqeq12d
    @4
    c0
    cI
    cid
    cfv
    #
    cop
    #
    wceq
    #
    @7
    @4
    c0
    vi
    vv
    com
    cvv
    vi
    cv
    #
    csuc
    #
    @32
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
    @30
    crdg
    #
    cfv
    @30
    c0
    cQ
    @38
    seqomlem.a
    fveq1i
    @30
    @37
    c0
    @29
    opex
    rdg0
    eqtri
    @31
    @30
    c0
    @30
    c2nd
    cfv
    #
    cop
    @4
    @6
    @29
    @39
    c0
    @39
    @29
    c0
    @29
    0ex
    cI
    cid
    fvex
    op2nd
    eqcomi
    opeq2i
    @31
    id
    @31
    @5
    @39
    c0
    @4
    @30
    c2nd
    fveq2
    opeq2d
    3eqtr4a
    ax-mp
    @8
    com
    wcel
    #
    @12
    @9
    @37
    cfv
    #
    @13
    @41
    c2nd
    cfv
    #
    cop
    #
    wceq
    #
    @17
    @40
    @12
    @41
    @13
    @8
    @10
    cF
    co
    #
    cop
    #
    wceq
    #
    @44
    @40
    @47
    @12
    @11
    @37
    cfv
    #
    @46
    wceq
    @40
    @48
    @8
    @10
    @37
    co
    #
    @46
    @8
    @10
    @37
    df-ov
    @40
    @10
    cvv
    wcel
    @49
    @46
    wceq
    @9
    c2nd
    fvex
    vi
    vv
    @8
    @10
    com
    cvv
    @36
    @46
    @37
    @13
    @8
    @34
    cF
    co
    #
    cop
    @32
    @8
    wceq
    @33
    @13
    @35
    @50
    @32
    @8
    suceq
    @32
    @8
    @34
    cF
    oveq1
    opeq12d
    @34
    @10
    wceq
    @50
    @45
    @13
    @34
    @10
    @8
    cF
    oveq2
    opeq2d
    @37
    eqid
    @13
    @45
    opex
    ovmpt2
    mpan2
    syl5eqr
    @12
    @41
    @48
    @46
    @9
    @11
    @37
    fveq2
    eqeq1d
    syl5ibrcom
    @40
    @44
    @47
    @46
    @13
    @46
    c2nd
    cfv
    #
    cop
    #
    wceq
    @40
    @45
    @51
    @13
    @45
    @51
    wceq
    @40
    @51
    @45
    @13
    @45
    @8
    vb
    vex
    sucex
    @8
    @10
    cF
    ovex
    op2nd
    eqcomi
    a1i
    opeq2d
    @47
    @41
    @46
    @43
    @52
    @47
    id
    @47
    @42
    @51
    @13
    @41
    @46
    c2nd
    fveq2
    opeq2d
    eqeq12d
    syl5ibrcom
    syld
    @40
    @14
    @41
    @16
    @43
    @40
    @13
    @38
    com
    cres
    #
    cfv
    #
    @8
    @53
    cfv
    #
    @37
    cfv
    @14
    @41
    @30
    @8
    @37
    frsuc
    @40
    @54
    @13
    @38
    cfv
    #
    @14
    @40
    @13
    com
    wcel
    @54
    @56
    wceq
    @8
    peano2
    @13
    com
    @38
    fvres
    syl
    @13
    cQ
    @38
    seqomlem.a
    fveq1i
    syl6eqr
    @40
    @55
    @9
    @37
    @40
    @55
    @8
    @38
    cfv
    @9
    @8
    com
    @38
    fvres
    @8
    cQ
    @38
    seqomlem.a
    fveq1i
    syl6eqr
    fveq2d
    3eqtr3d
    #
    @40
    @15
    @42
    @13
    @40
    @14
    @41
    c2nd
    @57
    fveq2d
    opeq2d
    eqeq12d
    sylibrd
    finds
end
