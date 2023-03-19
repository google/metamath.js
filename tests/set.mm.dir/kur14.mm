include "wss.mm"
include "ctop.mm"
include "wcel.mm"
include "cfn.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "c4.mm"
include "cdc.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "c0.mm"
include "cif.mm"
include "cv.mm"
include "cdif.mm"
include "cpr.mm"
include "wral.mm"
include "cpw.mm"
include "crab.mm"
include "cint.mm"
include "csn.mm"
include "cuni.mm"
include "ccl.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "rabbidv.mm"
include "inteqd.mm"
include "syl5eq.mm"
include "eleq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "unieq.mm"
include "pweqd.mm"
include "sseq2d.mm"
include "cvv.mm"
include "sn0top.mm"
include "elimel.mm"
include "uniexg.mm"
include "ax-mp.mm"
include "elpw2.mm"
include "syl6bbr.mm"
include "ifbid.mm"
include "difeq1d.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "preq12d.mm"
include "sseq1d.mm"
include "ralbidv.mm"
include "rabeqbidv.mm"
include "eqid.mm"
include "0elpw.mm"
include "elpwi.mm"
include "kur14lem10.mm"
include "dedth2h.mm"
include "ancoms.mm"

theorem kur14
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cS: class S
  let cJ: class J
  let cK: class K
  let cX: class X
  assume kur14.x: |- X = U. J
  assume kur14.k: |- K = ( cls ` J )
  assume kur14.s: |- S = |^| { x e. ~P ~P X | ( A e. x /\ A. y e. x { ( X \ y ) , ( K ` y ) } C_ x ) }

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint J x
  disjoint J y
  disjoint X x
  assert |- ( ( J e. Top /\ A C_ X ) -> ( S e. Fin /\ ( # ` S ) <_ ; 1 4 ) )

  proof
    cA
    cX
    wss
    #
    cJ
    ctop
    wcel
    #
    cS
    cfn
    wcel
    #
    cS
    chash
    cfv
    #
    c1
    c4
    cdc
    #
    cle
    wbr
    #
    wa
    #
    @0
    @1
    @6
    @0
    cA
    c0
    cif
    #
    vx
    cv
    #
    wcel
    #
    cX
    vy
    cv
    #
    cdif
    #
    @10
    cK
    cfv
    #
    cpr
    #
    @8
    wss
    #
    vy
    @8
    wral
    #
    wa
    #
    vx
    cX
    cpw
    #
    cpw
    #
    crab
    #
    cint
    #
    cfn
    wcel
    #
    @20
    chash
    cfv
    #
    @4
    cle
    wbr
    #
    wa
    cA
    @1
    cJ
    c0
    csn
    #
    cif
    #
    cuni
    #
    cpw
    #
    wcel
    #
    cA
    c0
    cif
    #
    @8
    wcel
    #
    @26
    @10
    cdif
    #
    @10
    @25
    ccl
    cfv
    #
    cfv
    #
    cpr
    #
    @8
    wss
    #
    vy
    @8
    wral
    #
    wa
    #
    vx
    @27
    cpw
    #
    crab
    #
    cint
    #
    cfn
    wcel
    #
    @40
    chash
    cfv
    #
    @4
    cle
    wbr
    #
    wa
    cA
    cJ
    c0
    @24
    cA
    @7
    wceq
    #
    @2
    @21
    @5
    @23
    @44
    cS
    @20
    cfn
    @44
    cS
    cA
    @8
    wcel
    #
    @15
    wa
    #
    vx
    @18
    crab
    #
    cint
    @20
    kur14.s
    @44
    @47
    @19
    @44
    @46
    @16
    vx
    @18
    @44
    @45
    @9
    @15
    cA
    @7
    @8
    eleq1
    anbi1d
    rabbidv
    inteqd
    syl5eq
    #
    eleq1d
    @44
    @3
    @22
    @4
    cle
    @44
    cS
    @20
    chash
    @48
    fveq2d
    breq1d
    anbi12d
    cJ
    @25
    wceq
    #
    @21
    @41
    @23
    @43
    @49
    @20
    @40
    cfn
    @49
    @19
    @39
    @49
    @16
    @37
    vx
    @18
    @38
    @49
    @17
    @27
    @49
    cX
    @26
    @49
    cX
    cJ
    cuni
    @26
    kur14.x
    cJ
    @25
    unieq
    syl5eq
    #
    pweqd
    pweqd
    @49
    @9
    @30
    @15
    @36
    @49
    @7
    @29
    @8
    @49
    @0
    @28
    cA
    c0
    @49
    @0
    cA
    @26
    wss
    @28
    @49
    cX
    @26
    cA
    @50
    sseq2d
    cA
    @26
    @25
    ctop
    wcel
    @26
    cvv
    wcel
    cJ
    @24
    ctop
    sn0top
    elimel
    #
    @25
    ctop
    uniexg
    ax-mp
    elpw2
    syl6bbr
    ifbid
    eleq1d
    @49
    @14
    @35
    vy
    @8
    @49
    @13
    @34
    @8
    @49
    @11
    @31
    @12
    @33
    @49
    cX
    @26
    @10
    @50
    difeq1d
    @49
    @10
    cK
    @32
    @49
    cK
    cJ
    ccl
    cfv
    @32
    kur14.k
    cJ
    @25
    ccl
    fveq2
    syl5eq
    fveq1d
    preq12d
    sseq1d
    ralbidv
    anbi12d
    rabeqbidv
    inteqd
    #
    eleq1d
    @49
    @22
    @42
    @4
    cle
    @49
    @20
    @40
    chash
    @52
    fveq2d
    breq1d
    anbi12d
    vx
    vy
    @29
    @40
    @25
    @32
    @26
    @51
    @26
    eqid
    @32
    eqid
    @40
    eqid
    @29
    @27
    wcel
    @29
    @26
    wss
    cA
    c0
    @27
    @26
    0elpw
    elimel
    @29
    @26
    elpwi
    ax-mp
    kur14lem10
    dedth2h
    ancoms
end
