include "cvv.mm"
include "wcel.mm"
include "ctc.mm"
include "cfv.mm"
include "crn.mm"
include "cuni.mm"
include "wceq.mm"
include "cv.mm"
include "fveq2.mm"
include "rneqd.mm"
include "unieqd.mm"
include "eqeq12d.mm"
include "wss.mm"
include "wtr.mm"
include "c0.mm"
include "vex.mm"
include "ituni0.mm"
include "ax-mp.mm"
include "fvssunirn.mm"
include "eqsstr3i.mm"
include "dftr3.mm"
include "com.mm"
include "wrex.mm"
include "wfn.mm"
include "wb.mm"
include "itunifn.mm"
include "fnunirn.mm"
include "mp2b.mm"
include "elssuni.mm"
include "csuc.mm"
include "itunisuc.mm"
include "syl6ss.mm"
include "rexlimivw.mm"
include "sylbi.mm"
include "mprgbir.mm"
include "wa.mm"
include "wi.mm"
include "tcmin.mm"
include "mp2an.mm"
include "unissb.mm"
include "fvelrnb.mm"
include "itunitc1.mm"
include "a1i.mm"
include "sseq1.mm"
include "syl5ibcom.mm"
include "rexlimiv.mm"
include "eqssi.mm"
include "vtoclg.mm"
include "wn.mm"
include "rn0.mm"
include "unieqi.mm"
include "uni0.mm"
include "eqtr2i.mm"
include "fvprc.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem itunitc
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cU: class U
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
  assert |- ( TC ` A ) = U. ran ( U ` A )

  proof
    cA
    cvv
    wcel
    #
    cA
    ctc
    cfv
    #
    cA
    cU
    cfv
    #
    crn
    #
    cuni
    #
    wceq
    #
    va
    cv
    #
    ctc
    cfv
    #
    @6
    cU
    cfv
    #
    crn
    #
    cuni
    #
    wceq
    @5
    va
    cA
    cvv
    @6
    cA
    wceq
    #
    @7
    @1
    @10
    @4
    @6
    cA
    ctc
    fveq2
    @11
    @9
    @3
    @11
    @8
    @2
    @6
    cA
    cU
    fveq2
    rneqd
    unieqd
    eqeq12d
    @7
    @10
    @6
    @10
    wss
    #
    @10
    wtr
    #
    @7
    @10
    wss
    #
    @6
    c0
    @8
    cfv
    #
    @10
    @6
    cvv
    wcel
    #
    @15
    @6
    wceq
    va
    vex
    #
    vx
    vy
    @6
    cU
    cvv
    ituni.u
    ituni0
    ax-mp
    @8
    c0
    fvssunirn
    eqsstr3i
    @13
    vb
    cv
    #
    @10
    wss
    #
    vb
    @10
    vb
    @10
    dftr3
    @18
    @10
    wcel
    #
    @18
    vc
    cv
    #
    @8
    cfv
    #
    wcel
    #
    vc
    com
    wrex
    #
    @19
    @16
    @8
    com
    wfn
    #
    @20
    @24
    wb
    @17
    vx
    vy
    @6
    cU
    cvv
    ituni.u
    itunifn
    #
    vc
    @18
    @8
    com
    fnunirn
    mp2b
    @23
    @19
    vc
    com
    @23
    @18
    @22
    cuni
    #
    @10
    @18
    @22
    elssuni
    @27
    @21
    csuc
    #
    @8
    cfv
    @10
    vx
    vy
    @6
    @21
    cU
    ituni.u
    itunisuc
    @8
    @28
    fvssunirn
    eqsstr3i
    syl6ss
    rexlimivw
    sylbi
    mprgbir
    @16
    @12
    @13
    wa
    @14
    wi
    @17
    @6
    @10
    cvv
    tcmin
    ax-mp
    mp2an
    @10
    @7
    wss
    @18
    @7
    wss
    #
    vb
    @9
    vb
    @9
    @7
    unissb
    @18
    @9
    wcel
    #
    @22
    @18
    wceq
    #
    vc
    com
    wrex
    #
    @29
    @16
    @25
    @30
    @32
    wb
    @17
    @26
    vc
    com
    @18
    @8
    fvelrnb
    mp2b
    @31
    @29
    vc
    com
    @21
    com
    wcel
    #
    @22
    @7
    wss
    #
    @31
    @29
    @34
    @33
    vx
    vy
    @6
    @21
    cU
    ituni.u
    itunitc1
    a1i
    @22
    @18
    @7
    sseq1
    syl5ibcom
    rexlimiv
    sylbi
    mprgbir
    eqssi
    vtoclg
    @0
    wn
    #
    c0
    c0
    crn
    #
    cuni
    #
    @1
    @4
    @37
    c0
    cuni
    c0
    @36
    c0
    rn0
    unieqi
    uni0
    eqtr2i
    cA
    ctc
    fvprc
    @35
    @3
    @36
    @35
    @2
    c0
    cA
    cU
    fvprc
    rneqd
    unieqd
    3eqtr4a
    pm2.61i
end
