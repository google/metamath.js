include "csuc.mm"
include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "iuneq1.mm"
include "eqeq12d.mm"
include "com.mm"
include "wcel.mm"
include "c0.mm"
include "suceq.mm"
include "fveq2d.mm"
include "iuneq2d.mm"
include "weq.mm"
include "cuni.mm"
include "uniiun.mm"
include "itunisuc.mm"
include "cvv.mm"
include "vex.mm"
include "ituni0.mm"
include "ax-mp.mm"
include "unieqi.mm"
include "eqtri.mm"
include "iuneq2i.mm"
include "3eqtr4i.mm"
include "wi.mm"
include "unieq.mm"
include "wel.mm"
include "a1i.mm"
include "iuncom4.mm"
include "eqtr2i.mm"
include "syl6eq.mm"
include "syl5eq.mm"
include "finds.mm"
include "wn.mm"
include "iun0.mm"
include "eqcomi.mm"
include "cdm.mm"
include "peano2b.mm"
include "wfn.mm"
include "itunifn.mm"
include "fndm.mm"
include "mp2b.mm"
include "eleq2i.mm"
include "bitr4i.mm"
include "ndmfv.mm"
include "sylnbi.mm"
include "sylnbir.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"
include "vtoclg.mm"

theorem ituniiun
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cU: class U
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume ituni.u: |- U = ( x e. _V |-> ( rec ( ( y e. _V |-> U. y ) , x ) |` _om ) )

  disjoint A x
  disjoint A y
  disjoint A a
  disjoint x y
  disjoint a x
  disjoint a y
  disjoint B x
  disjoint B y
  disjoint B a
  disjoint U a
  disjoint A b
  disjoint A c
  disjoint b x
  disjoint c x
  disjoint b y
  disjoint c y
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint d x
  disjoint d y
  disjoint a d
  disjoint b d
  disjoint c d
  disjoint U b
  disjoint U c
  disjoint U d
  assert |- ( A e. V -> ( ( U ` A ) ` suc B ) = U_ a e. A ( ( U ` a ) ` B ) )

  proof
    cB
    csuc
    #
    vb
    cv
    #
    cU
    cfv
    #
    cfv
    #
    va
    @1
    cB
    va
    cv
    #
    cU
    cfv
    #
    cfv
    #
    ciun
    #
    wceq
    #
    @0
    cA
    cU
    cfv
    #
    cfv
    #
    va
    cA
    @6
    ciun
    #
    wceq
    vb
    cA
    cV
    @1
    cA
    wceq
    #
    @3
    @10
    @7
    @11
    @12
    @0
    @2
    @9
    @1
    cA
    cU
    fveq2
    fveq1d
    va
    @1
    cA
    @6
    iuneq1
    eqeq12d
    cB
    com
    wcel
    #
    @8
    vd
    cv
    #
    csuc
    #
    @2
    cfv
    #
    va
    @1
    @14
    @5
    cfv
    #
    ciun
    #
    wceq
    c0
    csuc
    #
    @2
    cfv
    #
    va
    @1
    c0
    @5
    cfv
    #
    ciun
    #
    wceq
    vc
    cv
    #
    csuc
    #
    @2
    cfv
    #
    va
    @1
    @23
    @5
    cfv
    #
    ciun
    #
    wceq
    #
    @24
    csuc
    #
    @2
    cfv
    #
    va
    @1
    @24
    @5
    cfv
    #
    ciun
    #
    wceq
    #
    @8
    vd
    vc
    cB
    @14
    c0
    wceq
    #
    @16
    @20
    @18
    @22
    @34
    @15
    @19
    @2
    @14
    c0
    suceq
    fveq2d
    @34
    va
    @1
    @17
    @21
    @14
    c0
    @5
    fveq2
    iuneq2d
    eqeq12d
    vd
    vc
    weq
    #
    @16
    @25
    @18
    @27
    @35
    @15
    @24
    @2
    @14
    @23
    suceq
    fveq2d
    @35
    va
    @1
    @17
    @26
    @14
    @23
    @5
    fveq2
    iuneq2d
    eqeq12d
    @14
    @24
    wceq
    #
    @16
    @30
    @18
    @32
    @36
    @15
    @29
    @2
    @14
    @24
    suceq
    fveq2d
    @36
    va
    @1
    @17
    @31
    @14
    @24
    @5
    fveq2
    iuneq2d
    eqeq12d
    @14
    cB
    wceq
    #
    @16
    @3
    @18
    @7
    @37
    @15
    @0
    @2
    @14
    cB
    suceq
    fveq2d
    @37
    va
    @1
    @17
    @6
    @14
    cB
    @5
    fveq2
    iuneq2d
    eqeq12d
    @1
    cuni
    #
    va
    @1
    @4
    ciun
    @20
    @22
    va
    @1
    uniiun
    @20
    c0
    @2
    cfv
    #
    cuni
    @38
    vx
    vy
    @1
    c0
    cU
    ituni.u
    itunisuc
    @39
    @1
    @1
    cvv
    wcel
    #
    @39
    @1
    wceq
    vb
    vex
    #
    vx
    vy
    @1
    cU
    cvv
    ituni.u
    ituni0
    ax-mp
    unieqi
    eqtri
    va
    @1
    @21
    @4
    vx
    vy
    @4
    cU
    @1
    ituni.u
    ituni0
    iuneq2i
    3eqtr4i
    @28
    @33
    wi
    @23
    com
    wcel
    @28
    @30
    @25
    cuni
    #
    @32
    vx
    vy
    @1
    @24
    cU
    ituni.u
    itunisuc
    @28
    @42
    @27
    cuni
    #
    @32
    @25
    @27
    unieq
    @32
    va
    @1
    @26
    cuni
    #
    ciun
    @43
    va
    @1
    @31
    @44
    @31
    @44
    wceq
    va
    vb
    wel
    vx
    vy
    @4
    @23
    cU
    ituni.u
    itunisuc
    a1i
    iuneq2i
    va
    @1
    @26
    iuncom4
    eqtr2i
    syl6eq
    syl5eq
    a1i
    finds
    @13
    wn
    #
    c0
    va
    @1
    c0
    ciun
    #
    @3
    @7
    @46
    c0
    va
    @1
    iun0
    eqcomi
    @13
    @0
    @2
    cdm
    #
    wcel
    #
    @3
    c0
    wceq
    @13
    @0
    com
    wcel
    @48
    cB
    peano2b
    @47
    com
    @0
    @40
    @2
    com
    wfn
    @47
    com
    wceq
    @41
    vx
    vy
    @1
    cU
    cvv
    ituni.u
    itunifn
    com
    @2
    fndm
    mp2b
    eleq2i
    bitr4i
    @0
    @2
    ndmfv
    sylnbi
    @45
    va
    @1
    @6
    c0
    @13
    cB
    @5
    cdm
    #
    wcel
    @6
    c0
    wceq
    @49
    com
    cB
    @4
    cvv
    wcel
    @5
    com
    wfn
    @49
    com
    wceq
    va
    vex
    vx
    vy
    @4
    cU
    cvv
    ituni.u
    itunifn
    com
    @5
    fndm
    mp2b
    eleq2i
    cB
    @5
    ndmfv
    sylnbir
    iuneq2d
    3eqtr4a
    pm2.61i
    vtoclg
end
