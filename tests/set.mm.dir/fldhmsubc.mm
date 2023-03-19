include "wcel.mm"
include "cringc.mm"
include "cfv.mm"
include "cresc.mm"
include "co.mm"
include "csubc.mm"
include "cssc.mm"
include "wbr.mm"
include "cfield.mm"
include "cv.mm"
include "crg.mm"
include "cdr.mm"
include "ccrg.mm"
include "cin.mm"
include "elin.mm"
include "simprbi.mm"
include "crngring.mm"
include "syl.mm"
include "df-field.mm"
include "eleq2s.mm"
include "rgen.mm"
include "srhmsubc.mm"
include "wss.mm"
include "wral.mm"
include "inss1.mm"
include "eqsstri.mm"
include "sslin.mm"
include "ax-mp.mm"
include "a1i.mm"
include "sseq12i.mm"
include "sylibr.mm"
include "wa.mm"
include "crh.mm"
include "ssid.mm"
include "cvv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "weq.mm"
include "oveq12.mm"
include "adantl.mm"
include "simprl.mm"
include "simpr.mm"
include "ovexd.mm"
include "ovmpt2d.mm"
include "mpbir.mm"
include "sseli.mm"
include "ad2antrl.mm"
include "3sstr4d.mm"
include "ralrimivva.mm"
include "cxp.mm"
include "wfn.mm"
include "ovex.mm"
include "fnmpt2i.mm"
include "inex1g.mm"
include "syl5eqel.mm"
include "isssc.mm"
include "mpbir2and.mm"
include "wb.mm"
include "drhmsubc.mm"
include "eqid.mm"
include "subsubc.mm"

theorem fldhmsubc
  let cC: class C
  let cD: class D
  let cU: class U
  let cF: class F
  let cJ: class J
  let cV: class V
  let vs: setvar s
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume drhmsubc.c: |- C = ( U i^i DivRing )
  assume drhmsubc.j: |- J = ( r e. C , s e. C |-> ( r RingHom s ) )
  assume fldhmsubc.d: |- D = ( U i^i Field )
  assume fldhmsubc.f: |- F = ( r e. D , s e. D |-> ( r RingHom s ) )

  disjoint C r
  disjoint C s
  disjoint r s
  disjoint U r
  disjoint U s
  disjoint V r
  disjoint V s
  disjoint D r
  disjoint D s
  disjoint D x
  disjoint D y
  disjoint r x
  disjoint r y
  disjoint s x
  disjoint s y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint J x
  disjoint J y
  disjoint U x
  disjoint U y
  disjoint V x
  disjoint V y
  disjoint k x
  assert |- ( U e. V -> F e. ( Subcat ` ( ( RingCat ` U ) |`cat J ) ) )

  proof
    cU
    cV
    wcel
    #
    cF
    cU
    cringc
    cfv
    #
    cJ
    cresc
    co
    #
    csubc
    cfv
    wcel
    #
    cF
    @1
    csubc
    cfv
    #
    wcel
    #
    cF
    cJ
    cssc
    wbr
    #
    cD
    cfield
    cU
    cF
    cV
    vs
    vr
    vr
    cv
    #
    crg
    wcel
    #
    vr
    cfield
    @8
    @7
    cdr
    ccrg
    cin
    #
    cfield
    @7
    @9
    wcel
    #
    @7
    ccrg
    wcel
    #
    @8
    @10
    @7
    cdr
    wcel
    @11
    @7
    cdr
    ccrg
    elin
    simprbi
    @7
    crngring
    syl
    df-field
    eleq2s
    rgen
    fldhmsubc.d
    fldhmsubc.f
    srhmsubc
    @0
    @6
    cD
    cC
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    cF
    co
    #
    @13
    @14
    cJ
    co
    #
    wss
    #
    vy
    cD
    wral
    vx
    cD
    wral
    @0
    cU
    cfield
    cin
    #
    cU
    cdr
    cin
    #
    wss
    #
    @12
    @20
    @0
    cfield
    cdr
    wss
    @20
    cfield
    @9
    cdr
    df-field
    cdr
    ccrg
    inss1
    eqsstri
    cfield
    cdr
    cU
    sslin
    ax-mp
    #
    a1i
    cD
    @18
    cC
    @19
    fldhmsubc.d
    drhmsubc.c
    sseq12i
    #
    sylibr
    @0
    @17
    vx
    vy
    cD
    cD
    @0
    @13
    cD
    wcel
    #
    @14
    cD
    wcel
    #
    wa
    #
    wa
    #
    @13
    @14
    crh
    co
    #
    @27
    @15
    @16
    @27
    @27
    wss
    @26
    @27
    ssid
    a1i
    @26
    vr
    vs
    @13
    @14
    cD
    cD
    @7
    vs
    cv
    #
    crh
    co
    #
    @27
    cF
    cvv
    cF
    vr
    vs
    cD
    cD
    @29
    cmpt2
    wceq
    @26
    fldhmsubc.f
    a1i
    vr
    vx
    weq
    vs
    vy
    weq
    wa
    @29
    @27
    wceq
    @26
    @7
    @13
    @28
    @14
    crh
    oveq12
    adantl
    #
    @0
    @23
    @24
    simprl
    @25
    @24
    @0
    @23
    @24
    simpr
    adantl
    @26
    @13
    @14
    crh
    ovexd
    #
    ovmpt2d
    @26
    vr
    vs
    @13
    @14
    cC
    cC
    @29
    @27
    cJ
    cvv
    cJ
    vr
    vs
    cC
    cC
    @29
    cmpt2
    wceq
    @26
    drhmsubc.j
    a1i
    @30
    @23
    @13
    cC
    wcel
    @0
    @24
    cD
    cC
    @13
    @12
    @20
    @21
    @22
    mpbir
    #
    sseli
    ad2antrl
    @25
    @14
    cC
    wcel
    #
    @0
    @24
    @33
    @23
    cD
    cC
    @14
    @32
    sseli
    adantl
    adantl
    @31
    ovmpt2d
    3sstr4d
    ralrimivva
    @0
    vx
    vy
    cD
    cC
    cF
    cJ
    cvv
    cF
    cD
    cD
    cxp
    wfn
    @0
    vr
    vs
    cD
    cD
    @29
    cF
    fldhmsubc.f
    @7
    @28
    crh
    ovex
    #
    fnmpt2i
    a1i
    cJ
    cC
    cC
    cxp
    wfn
    @0
    vr
    vs
    cC
    cC
    @29
    cJ
    drhmsubc.j
    @34
    fnmpt2i
    a1i
    @0
    cC
    @19
    cvv
    drhmsubc.c
    cU
    cdr
    cV
    inex1g
    syl5eqel
    isssc
    mpbir2and
    @0
    cJ
    @4
    wcel
    @3
    @5
    @6
    wa
    wb
    cC
    cU
    cJ
    cV
    vs
    vr
    drhmsubc.c
    drhmsubc.j
    drhmsubc
    @1
    @2
    cJ
    cF
    @2
    eqid
    subsubc
    syl
    mpbir2and
end
