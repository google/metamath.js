include "wcel.mm"
include "wlim.mm"
include "wa.mm"
include "cfv.mm"
include "cres.mm"
include "crn.mm"
include "cuni.mm"
include "cima.mm"
include "wceq.mm"
include "cv.mm"
include "fveq2.mm"
include "reseq2.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "vtoclga.mm"
include "adantr.mm"
include "c0.mm"
include "cdm.mm"
include "cif.mm"
include "cvv.mm"
include "eleq1d.mm"
include "simpr.mm"
include "wn.mm"
include "nlim0.mm"
include "wb.mm"
include "cin.mm"
include "dmres.mm"
include "wss.mm"
include "word.mm"
include "ordelss.mm"
include "mpan.mm"
include "wfn.mm"
include "fndm.mm"
include "ax-mp.mm"
include "syl6sseqr.mm"
include "df-ss.mm"
include "sylib.mm"
include "syl5eq.mm"
include "dmeq.mm"
include "dm0.mm"
include "syl6eq.mm"
include "sylan9req.mm"
include "limeq.mm"
include "syl.mm"
include "mtbiri.mm"
include "ex.mm"
include "mt2d.mm"
include "iffalsed.mm"
include "mpbird.mm"
include "iftrued.mm"
include "eqtrd.mm"
include "rnexg.mm"
include "uniexg.mm"
include "3syl.mm"
include "eqeltrd.mm"
include "eqeq1.mm"
include "rneq.mm"
include "unieqd.mm"
include "fveq1.mm"
include "ifbieq12d.mm"
include "ifbieq2d.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "df-ima.mm"
include "unieqi.mm"
include "syl6eqr.mm"

theorem tz7.44-3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  assume tz7.44.1: |- G = ( x e. _V |-> if ( x = (/) , A , if ( Lim dom x , U. ran x , ( H ` ( x ` U. dom x ) ) ) ) )
  assume tz7.44.2: |- ( y e. X -> ( F ` y ) = ( G ` ( F |` y ) ) )
  assume tz7.44.3: |- ( y e. X -> ( F |` y ) e. _V )
  assume tz7.44.4: |- F Fn X
  assume tz7.44.5: |- Ord X

  disjoint A x
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint G y
  disjoint H x
  disjoint X y
  assert |- ( ( B e. X /\ Lim B ) -> ( F ` B ) = U. ( F " B ) )

  proof
    cB
    cX
    wcel
    #
    cB
    wlim
    #
    wa
    #
    cB
    cF
    cfv
    #
    cF
    cB
    cres
    #
    crn
    #
    cuni
    #
    cF
    cB
    cima
    #
    cuni
    @2
    @3
    @4
    cG
    cfv
    #
    @6
    @0
    @3
    @8
    wceq
    #
    @1
    vy
    cv
    #
    cF
    cfv
    #
    cF
    @10
    cres
    #
    cG
    cfv
    #
    wceq
    @9
    vy
    cB
    cX
    @10
    cB
    wceq
    #
    @11
    @3
    @13
    @8
    @10
    cB
    cF
    fveq2
    @14
    @12
    @4
    cG
    @10
    cB
    cF
    reseq2
    #
    fveq2d
    eqeq12d
    tz7.44.2
    vtoclga
    adantr
    @2
    @8
    @4
    c0
    wceq
    #
    cA
    @4
    cdm
    #
    wlim
    #
    @6
    @17
    cuni
    #
    @4
    cfv
    #
    cH
    cfv
    #
    cif
    #
    cif
    #
    @6
    @2
    @4
    cvv
    wcel
    #
    @23
    cvv
    wcel
    @8
    @23
    wceq
    @0
    @24
    @1
    @12
    cvv
    wcel
    @24
    vy
    cB
    cX
    @14
    @12
    @4
    cvv
    @15
    eleq1d
    tz7.44.3
    vtoclga
    adantr
    #
    @2
    @23
    @6
    cvv
    @2
    @23
    @22
    @6
    @2
    @16
    cA
    @22
    @2
    @16
    @1
    @0
    @1
    simpr
    #
    @2
    @16
    @1
    wn
    @2
    @16
    wa
    #
    @1
    c0
    wlim
    #
    nlim0
    @27
    cB
    c0
    wceq
    @1
    @28
    wb
    @2
    @16
    cB
    @17
    c0
    @2
    @17
    cB
    cF
    cdm
    #
    cin
    #
    cB
    cF
    cB
    dmres
    @2
    cB
    @29
    wss
    @30
    cB
    wceq
    @2
    cB
    cX
    @29
    @0
    cB
    cX
    wss
    #
    @1
    cX
    word
    @0
    @31
    tz7.44.5
    cX
    cB
    ordelss
    mpan
    adantr
    cF
    cX
    wfn
    @29
    cX
    wceq
    tz7.44.4
    cX
    cF
    fndm
    ax-mp
    syl6sseqr
    cB
    @29
    df-ss
    sylib
    syl5eq
    #
    @16
    @17
    c0
    cdm
    c0
    @4
    c0
    dmeq
    dm0
    syl6eq
    sylan9req
    cB
    c0
    limeq
    syl
    mtbiri
    ex
    mt2d
    iffalsed
    @2
    @18
    @6
    @21
    @2
    @18
    @1
    @26
    @2
    @17
    cB
    wceq
    @18
    @1
    wb
    @32
    @17
    cB
    limeq
    syl
    mpbird
    iftrued
    eqtrd
    #
    @2
    @24
    @5
    cvv
    wcel
    @6
    cvv
    wcel
    @25
    @4
    cvv
    rnexg
    @5
    cvv
    uniexg
    3syl
    eqeltrd
    vx
    @4
    vx
    cv
    #
    c0
    wceq
    #
    cA
    @34
    cdm
    #
    wlim
    #
    @34
    crn
    #
    cuni
    #
    @36
    cuni
    #
    @34
    cfv
    #
    cH
    cfv
    #
    cif
    #
    cif
    @23
    cvv
    cvv
    cG
    @34
    @4
    wceq
    #
    @35
    @16
    @43
    @22
    cA
    @34
    @4
    c0
    eqeq1
    @44
    @37
    @18
    @39
    @42
    @6
    @21
    @44
    @36
    @17
    wceq
    @37
    @18
    wb
    @34
    @4
    dmeq
    #
    @36
    @17
    limeq
    syl
    @44
    @38
    @5
    @34
    @4
    rneq
    unieqd
    @44
    @41
    @20
    cH
    @44
    @41
    @40
    @4
    cfv
    @20
    @40
    @34
    @4
    fveq1
    @44
    @40
    @19
    @4
    @44
    @36
    @17
    @45
    unieqd
    fveq2d
    eqtrd
    fveq2d
    ifbieq12d
    ifbieq2d
    tz7.44.1
    fvmptg
    syl2anc
    @33
    eqtrd
    eqtrd
    @7
    @5
    cF
    cB
    df-ima
    unieqi
    syl6eqr
end
