include "wcel.mm"
include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "cpw.mm"
include "ctg.mm"
include "cfv.mm"
include "ciin.mm"
include "cin.mm"
include "cfne.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "unitg.mm"
include "adantl.mm"
include "unieq.mm"
include "eqeq2d.mm"
include "rspccva.mm"
include "3ad2antl2.mm"
include "eqtr4d.mm"
include "eqimss.mm"
include "syl.mm"
include "sspwuni.mm"
include "sylibr.mm"
include "ralrimiva.mm"
include "ne0i.mm"
include "3ad2ant3.mm"
include "riinn0.mm"
include "syl2anc.mm"
include "wbr.mm"
include "wrex.mm"
include "simp3.mm"
include "ssid.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "rspcev.mm"
include "sylancl.mm"
include "iinss.mm"
include "unissd.mm"
include "sseqtrd.mm"
include "3adant1.mm"
include "adantr.mm"
include "eqtr3d.mm"
include "simpr.mm"
include "eltg3i.mm"
include "eqeltrd.mm"
include "cvv.mm"
include "wb.mm"
include "uniexg.mm"
include "eliin.mm"
include "mpbird.mm"
include "elssuni.mm"
include "eqssd.mm"
include "eqid.mm"
include "isfne4.mm"
include "sylanbrc.mm"
include "eqbrtrd.mm"

theorem fnemeet1
  let vy: setvar y
  let vt: setvar t
  let cA: class A
  let cS: class S
  let cV: class V
  let cX: class X
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let cT: class T

  disjoint t y
  disjoint A t
  disjoint A y
  disjoint S t
  disjoint S y
  disjoint V t
  disjoint X t
  disjoint X y
  disjoint j k
  disjoint j t
  disjoint j x
  disjoint j y
  disjoint S j
  disjoint k t
  disjoint k x
  disjoint k y
  disjoint S k
  disjoint t x
  disjoint x y
  disjoint S x
  disjoint V j
  disjoint V k
  disjoint V x
  disjoint X j
  disjoint X k
  disjoint X x
  disjoint T t
  disjoint T x
  assert |- ( ( X e. V /\ A. y e. S X = U. y /\ A e. S ) -> ( ~P X i^i |^|_ t e. S ( topGen ` t ) ) Fne A )

  proof
    cX
    cV
    wcel
    #
    cX
    vy
    cv
    #
    cuni
    #
    wceq
    #
    vy
    cS
    wral
    #
    cA
    cS
    wcel
    #
    w3a
    #
    cX
    cpw
    #
    vt
    cS
    vt
    cv
    #
    ctg
    cfv
    #
    ciin
    #
    cin
    #
    @10
    cA
    cfne
    @6
    @9
    @7
    wss
    #
    vt
    cS
    wral
    cS
    c0
    wne
    #
    @11
    @10
    wceq
    @6
    @12
    vt
    cS
    @6
    @8
    cS
    wcel
    #
    wa
    #
    @9
    cuni
    #
    cX
    wss
    #
    @12
    @15
    @16
    cX
    wceq
    @17
    @15
    @16
    @8
    cuni
    #
    cX
    @14
    @16
    @18
    wceq
    @6
    @8
    cS
    unitg
    adantl
    @4
    @0
    @14
    cX
    @18
    wceq
    #
    @5
    @3
    @19
    vy
    @8
    cS
    @1
    @8
    wceq
    @2
    @18
    cX
    @1
    @8
    unieq
    eqeq2d
    rspccva
    3ad2antl2
    #
    eqtr4d
    @16
    cX
    eqimss
    syl
    @9
    cX
    sspwuni
    sylibr
    ralrimiva
    @5
    @0
    @13
    @4
    cS
    cA
    ne0i
    3ad2ant3
    vt
    @7
    @9
    cS
    riinn0
    syl2anc
    @6
    @10
    cuni
    #
    cA
    cuni
    #
    wceq
    @10
    cA
    ctg
    cfv
    #
    wss
    #
    @10
    cA
    cfne
    wbr
    @6
    @21
    @22
    @6
    @21
    @23
    cuni
    #
    @22
    @6
    @10
    @23
    @6
    @9
    @23
    wss
    #
    vt
    cS
    wrex
    #
    @24
    @6
    @5
    @23
    @23
    wss
    #
    @27
    @0
    @4
    @5
    simp3
    @23
    ssid
    @26
    @28
    vt
    cA
    cS
    @8
    cA
    wceq
    @9
    @23
    @23
    @8
    cA
    ctg
    fveq2
    sseq1d
    rspcev
    sylancl
    vt
    cS
    @9
    @23
    iinss
    syl
    #
    unissd
    @5
    @0
    @25
    @22
    wceq
    @4
    cA
    cS
    unitg
    3ad2ant3
    sseqtrd
    @6
    @22
    @10
    wcel
    #
    @22
    @21
    wss
    @6
    @30
    @22
    @9
    wcel
    #
    vt
    cS
    wral
    #
    @6
    @31
    vt
    cS
    @15
    @22
    @18
    @9
    @15
    cX
    @22
    @18
    @6
    cX
    @22
    wceq
    #
    @14
    @4
    @5
    @33
    @0
    @3
    @33
    vy
    cA
    cS
    @1
    cA
    wceq
    @2
    @22
    cX
    @1
    cA
    unieq
    eqeq2d
    rspccva
    3adant1
    adantr
    @20
    eqtr3d
    @15
    @14
    @8
    @8
    wss
    @18
    @9
    wcel
    @6
    @14
    simpr
    @8
    ssid
    @8
    @8
    cS
    eltg3i
    sylancl
    eqeltrd
    ralrimiva
    @6
    @22
    cvv
    wcel
    #
    @30
    @32
    wb
    @5
    @0
    @34
    @4
    cA
    cS
    uniexg
    3ad2ant3
    vt
    @22
    cS
    @9
    cvv
    eliin
    syl
    mpbird
    @22
    @10
    elssuni
    syl
    eqssd
    @29
    @10
    cA
    @21
    @22
    @21
    eqid
    @22
    eqid
    isfne4
    sylanbrc
    eqbrtrd
end
