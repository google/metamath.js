include "cvv.mm"
include "wcel.mm"
include "cfv.mm"
include "ctc.mm"
include "wss.mm"
include "cv.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "sseq12d.mm"
include "com.mm"
include "c0.mm"
include "csuc.mm"
include "sseq1d.mm"
include "weq.mm"
include "vex.mm"
include "ituni0.mm"
include "tcid.mm"
include "eqsstrd.mm"
include "ax-mp.mm"
include "wi.mm"
include "cuni.mm"
include "itunisuc.mm"
include "cpw.mm"
include "wtr.mm"
include "tctr.mm"
include "pwtr.mm"
include "mpbi.mm"
include "trss.mm"
include "fvex.mm"
include "elpw.mm"
include "sspwuni.mm"
include "3imtr3i.mm"
include "syl5eqss.mm"
include "a1i.mm"
include "finds.mm"
include "wn.mm"
include "cdm.mm"
include "wfn.mm"
include "itunifn.mm"
include "fndm.mm"
include "mp2b.mm"
include "eleq2i.mm"
include "ndmfv.mm"
include "sylnbir.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "pm2.61i.mm"
include "vtoclg.mm"
include "fvprc.mm"
include "0fv.mm"
include "syl6eq.mm"

theorem itunitc1
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cU: class U
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume ituni.u: |- U = ( x e. _V |-> ( rec ( ( y e. _V |-> U. y ) , x ) |` _om ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
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
  assert |- ( ( U ` A ) ` B ) C_ ( TC ` A )

  proof
    cA
    cvv
    wcel
    #
    cB
    cA
    cU
    cfv
    #
    cfv
    #
    cA
    ctc
    cfv
    #
    wss
    #
    cB
    va
    cv
    #
    cU
    cfv
    #
    cfv
    #
    @5
    ctc
    cfv
    #
    wss
    #
    @4
    va
    cA
    cvv
    @5
    cA
    wceq
    #
    @7
    @2
    @8
    @3
    @10
    cB
    @6
    @1
    @5
    cA
    cU
    fveq2
    fveq1d
    @5
    cA
    ctc
    fveq2
    sseq12d
    cB
    com
    wcel
    #
    @9
    vb
    cv
    #
    @6
    cfv
    #
    @8
    wss
    c0
    @6
    cfv
    #
    @8
    wss
    #
    vc
    cv
    #
    @6
    cfv
    #
    @8
    wss
    #
    @16
    csuc
    #
    @6
    cfv
    #
    @8
    wss
    #
    @9
    vb
    vc
    cB
    @12
    c0
    wceq
    @13
    @14
    @8
    @12
    c0
    @6
    fveq2
    sseq1d
    vb
    vc
    weq
    @13
    @17
    @8
    @12
    @16
    @6
    fveq2
    sseq1d
    @12
    @19
    wceq
    @13
    @20
    @8
    @12
    @19
    @6
    fveq2
    sseq1d
    @12
    cB
    wceq
    @13
    @7
    @8
    @12
    cB
    @6
    fveq2
    sseq1d
    @5
    cvv
    wcel
    #
    @15
    va
    vex
    #
    @22
    @14
    @5
    @8
    vx
    vy
    @5
    cU
    cvv
    ituni.u
    ituni0
    @5
    cvv
    tcid
    eqsstrd
    ax-mp
    @18
    @21
    wi
    @16
    com
    wcel
    @18
    @20
    @17
    cuni
    #
    @8
    vx
    vy
    @5
    @16
    cU
    ituni.u
    itunisuc
    @17
    @8
    cpw
    #
    wcel
    #
    @17
    @25
    wss
    #
    @18
    @24
    @8
    wss
    @25
    wtr
    #
    @26
    @27
    wi
    @8
    wtr
    @28
    @5
    tctr
    @8
    pwtr
    mpbi
    @25
    @17
    trss
    ax-mp
    @17
    @8
    @16
    @6
    fvex
    elpw
    @17
    @8
    sspwuni
    3imtr3i
    syl5eqss
    a1i
    finds
    @11
    wn
    @7
    c0
    @8
    @11
    cB
    @6
    cdm
    #
    wcel
    @7
    c0
    wceq
    @29
    com
    cB
    @22
    @6
    com
    wfn
    @29
    com
    wceq
    @23
    vx
    vy
    @5
    cU
    cvv
    ituni.u
    itunifn
    com
    @6
    fndm
    mp2b
    eleq2i
    cB
    @6
    ndmfv
    sylnbir
    @8
    0ss
    syl6eqss
    pm2.61i
    vtoclg
    @0
    wn
    #
    @2
    c0
    @3
    @30
    @2
    cB
    c0
    cfv
    c0
    @30
    cB
    @1
    c0
    cA
    cU
    fvprc
    fveq1d
    cB
    0fv
    syl6eq
    @3
    0ss
    syl6eqss
    pm2.61i
end
