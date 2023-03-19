include "ciun.mm"
include "c2nd.mm"
include "cres.mm"
include "wfo.mm"
include "wfn.mm"
include "crn.mm"
include "wceq.mm"
include "cvv.mm"
include "wss.mm"
include "wf.mm"
include "fo2nd.mm"
include "fof.mm"
include "ffn.mm"
include "mp2b.mm"
include "ssv.mm"
include "fnssres.mm"
include "mp2an.mm"
include "cima.mm"
include "df-ima.mm"
include "cv.mm"
include "cfv.mm"
include "wrex.mm"
include "wcel.mm"
include "csn.mm"
include "cxp.mm"
include "eleq2i.mm"
include "eliun.mm"
include "bitri.mm"
include "xp2nd.mm"
include "eleq1.mm"
include "syl5ib.mm"
include "reximdv.mm"
include "syl5bi.mm"
include "impcom.mm"
include "rexlimiva.mm"
include "nfiu1.mm"
include "nfcxfr.mm"
include "nfv.mm"
include "nfrex.mm"
include "wa.mm"
include "cop.mm"
include "ssiun2.mm"
include "adantr.mm"
include "simpr.mm"
include "vsnid.mm"
include "opelxp.mm"
include "mpbiran.mm"
include "sylibr.mm"
include "sseldd.mm"
include "syl6eleqr.mm"
include "vex.mm"
include "op2nd.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "sylancl.mm"
include "ex.mm"
include "rexlimi.mm"
include "impbii.mm"
include "wb.mm"
include "fvelimab.mm"
include "3bitr4i.mm"
include "eqriv.mm"
include "eqtr3i.mm"
include "df-fo.mm"
include "mpbir2an.mm"

theorem iunfo
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let wph: wff ph
  assume iunfo.1: |- T = U_ x e. A ( { x } X. B )

  disjoint A x
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B f
  disjoint B g
  disjoint B y
  disjoint B z
  disjoint C f
  disjoint C g
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint T f
  disjoint T y
  disjoint T z
  disjoint f ph
  assert |- ( 2nd |` T ) : T -onto-> U_ x e. A B

  proof
    cT
    vx
    cA
    cB
    ciun
    #
    c2nd
    cT
    cres
    #
    wfo
    @1
    cT
    wfn
    #
    @1
    crn
    #
    @0
    wceq
    c2nd
    cvv
    wfn
    #
    cT
    cvv
    wss
    #
    @2
    cvv
    cvv
    c2nd
    wfo
    cvv
    cvv
    c2nd
    wf
    @4
    fo2nd
    cvv
    cvv
    c2nd
    fof
    cvv
    cvv
    c2nd
    ffn
    mp2b
    #
    cT
    ssv
    #
    cvv
    cT
    c2nd
    fnssres
    mp2an
    c2nd
    cT
    cima
    #
    @3
    @0
    c2nd
    cT
    df-ima
    vy
    @8
    @0
    vz
    cv
    #
    c2nd
    cfv
    #
    vy
    cv
    #
    wceq
    #
    vz
    cT
    wrex
    #
    @11
    cB
    wcel
    #
    vx
    cA
    wrex
    #
    @11
    @8
    wcel
    #
    @11
    @0
    wcel
    @13
    @15
    @12
    @15
    vz
    cT
    @12
    @9
    cT
    wcel
    #
    @15
    @17
    @9
    vx
    cv
    #
    csn
    #
    cB
    cxp
    #
    wcel
    #
    vx
    cA
    wrex
    #
    @12
    @15
    @17
    @9
    vx
    cA
    @20
    ciun
    #
    wcel
    @22
    cT
    @23
    @9
    iunfo.1
    eleq2i
    vx
    @9
    cA
    @20
    eliun
    bitri
    @12
    @21
    @14
    vx
    cA
    @21
    @10
    cB
    wcel
    @12
    @14
    @9
    @19
    cB
    xp2nd
    @10
    @11
    cB
    eleq1
    syl5ib
    reximdv
    syl5bi
    impcom
    rexlimiva
    @14
    @13
    vx
    cA
    @12
    vx
    vz
    cT
    vx
    cT
    @23
    iunfo.1
    vx
    cA
    @20
    nfiu1
    nfcxfr
    @12
    vx
    nfv
    nfrex
    @18
    cA
    wcel
    #
    @14
    @13
    @24
    @14
    wa
    #
    @18
    @11
    cop
    #
    cT
    wcel
    @26
    c2nd
    cfv
    #
    @11
    wceq
    #
    @13
    @25
    @26
    @23
    cT
    @25
    @20
    @23
    @26
    @24
    @20
    @23
    wss
    @14
    vx
    cA
    @20
    ssiun2
    adantr
    @25
    @14
    @26
    @20
    wcel
    #
    @24
    @14
    simpr
    @29
    @18
    @19
    wcel
    @14
    vx
    vsnid
    @18
    @11
    @19
    cB
    opelxp
    mpbiran
    sylibr
    sseldd
    iunfo.1
    syl6eleqr
    @18
    @11
    vx
    vex
    vy
    vex
    op2nd
    @12
    @28
    vz
    @26
    cT
    @9
    @26
    wceq
    @10
    @27
    @11
    @9
    @26
    c2nd
    fveq2
    eqeq1d
    rspcev
    sylancl
    ex
    rexlimi
    impbii
    @4
    @5
    @16
    @13
    wb
    @6
    @7
    vz
    cvv
    cT
    @11
    c2nd
    fvelimab
    mp2an
    vx
    @11
    cA
    cB
    eliun
    3bitr4i
    eqriv
    eqtr3i
    cT
    @0
    @1
    df-fo
    mpbir2an
end
