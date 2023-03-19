include "wcel.mm"
include "cpw.mm"
include "c0.mm"
include "cv.mm"
include "cin.mm"
include "cfn.mm"
include "wdisj.mm"
include "cdif.mm"
include "cuni.mm"
include "wceq.mm"
include "w3a.mm"
include "wrex.mm"
include "wa.mm"
include "wral.mm"
include "wss.mm"
include "rossspw.mm"
include "elpwg.mm"
include "mpbird.mm"
include "0elros.mm"
include "cun.mm"
include "crab.mm"
include "uneq1.mm"
include "eleq1d.mm"
include "difeq1.mm"
include "anbi12d.mm"
include "uneq2.mm"
include "difeq2.mm"
include "cbvral2v.mm"
include "anbi2i.mm"
include "rabbii.mm"
include "eqtr4i.mm"
include "inelros.mm"
include "3expb.mm"
include "csn.mm"
include "difelros.mm"
include "snssd.mm"
include "snex.mm"
include "elpw.mm"
include "sylibr.mm"
include "snfi.mm"
include "a1i.mm"
include "disjxsn.mm"
include "unisng.mm"
include "syl.mm"
include "eqcomd.mm"
include "eleq1.mm"
include "disjeq1.mm"
include "unieq.mm"
include "eqeq2d.mm"
include "3anbi123d.mm"
include "rspcev.mm"
include "syl13anc.mm"
include "jca.mm"
include "ralrimivva.mm"
include "3jca.mm"
include "issros.mm"

theorem rossros
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cQ: class Q
  let cS: class S
  let cN: class N
  let cO: class O
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  assume rossros.q: |- Q = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s A. y e. s ( ( x u. y ) e. s /\ ( x \ y ) e. s ) ) }
  assume rossros.n: |- N = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s A. y e. s ( ( x i^i y ) e. s /\ E. z e. ~P s ( z e. Fin /\ Disj_ t e. z t /\ ( x \ y ) = U. z ) ) ) }

  disjoint O s
  disjoint Q x
  disjoint Q y
  disjoint x y
  disjoint S s
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint x z
  disjoint y z
  disjoint s t
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint S u
  disjoint S v
  disjoint s u
  disjoint s v
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint v x
  disjoint v y
  disjoint v z
  assert |- ( S e. Q -> S e. N )

  proof
    cS
    cQ
    wcel
    #
    cS
    cO
    cpw
    #
    cpw
    #
    wcel
    #
    c0
    cS
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cin
    cS
    wcel
    #
    vz
    cv
    #
    cfn
    wcel
    #
    vt
    @8
    vt
    cv
    #
    wdisj
    #
    @5
    @6
    cdif
    #
    @8
    cuni
    #
    wceq
    #
    w3a
    #
    vz
    cS
    cpw
    #
    wrex
    #
    wa
    #
    vy
    cS
    wral
    vx
    cS
    wral
    #
    w3a
    cS
    cN
    wcel
    @0
    @3
    @4
    @19
    @0
    @3
    cS
    @1
    wss
    vx
    vy
    cQ
    cS
    cO
    vs
    rossros.q
    rossspw
    cS
    @1
    cQ
    elpwg
    mpbird
    vx
    vy
    cQ
    cS
    cO
    vs
    rossros.q
    0elros
    @0
    @18
    vx
    vy
    cS
    cS
    @0
    @5
    cS
    wcel
    #
    @6
    cS
    wcel
    #
    wa
    wa
    #
    @7
    @17
    @0
    @20
    @21
    @7
    vu
    vv
    @5
    @6
    cQ
    cS
    cO
    vs
    cQ
    c0
    vs
    cv
    #
    wcel
    #
    @5
    @6
    cun
    #
    @23
    wcel
    #
    @12
    @23
    wcel
    #
    wa
    #
    vy
    @23
    wral
    vx
    @23
    wral
    #
    wa
    #
    vs
    @2
    crab
    @24
    vu
    cv
    #
    vv
    cv
    #
    cun
    #
    @23
    wcel
    #
    @31
    @32
    cdif
    #
    @23
    wcel
    #
    wa
    #
    vv
    @23
    wral
    vu
    @23
    wral
    #
    wa
    #
    vs
    @2
    crab
    rossros.q
    @39
    @30
    vs
    @2
    @38
    @29
    @24
    @37
    @28
    @5
    @32
    cun
    #
    @23
    wcel
    #
    @5
    @32
    cdif
    #
    @23
    wcel
    #
    wa
    vu
    vv
    vx
    vy
    @23
    @23
    @31
    @5
    wceq
    #
    @34
    @41
    @36
    @43
    @44
    @33
    @40
    @23
    @31
    @5
    @32
    uneq1
    eleq1d
    @44
    @35
    @42
    @23
    @31
    @5
    @32
    difeq1
    eleq1d
    anbi12d
    @32
    @6
    wceq
    #
    @41
    @26
    @43
    @27
    @45
    @40
    @25
    @23
    @32
    @6
    @5
    uneq2
    eleq1d
    @45
    @42
    @12
    @23
    @32
    @6
    @5
    difeq2
    eleq1d
    anbi12d
    cbvral2v
    anbi2i
    rabbii
    eqtr4i
    #
    inelros
    3expb
    @22
    @12
    csn
    #
    @16
    wcel
    #
    @47
    cfn
    wcel
    #
    vt
    @47
    @10
    wdisj
    #
    @12
    @47
    cuni
    #
    wceq
    #
    @17
    @22
    @47
    cS
    wss
    @48
    @22
    @12
    cS
    @0
    @20
    @21
    @12
    cS
    wcel
    #
    vu
    vv
    @5
    @6
    cQ
    cS
    cO
    vs
    @46
    difelros
    3expb
    #
    snssd
    @47
    cS
    @12
    snex
    elpw
    sylibr
    @49
    @22
    @12
    snfi
    a1i
    @50
    @22
    vt
    @12
    @10
    disjxsn
    a1i
    @22
    @51
    @12
    @22
    @53
    @51
    @12
    wceq
    @54
    @12
    cS
    unisng
    syl
    eqcomd
    @15
    @49
    @50
    @52
    w3a
    vz
    @47
    @16
    @8
    @47
    wceq
    #
    @9
    @49
    @11
    @50
    @14
    @52
    @8
    @47
    cfn
    eleq1
    vt
    @8
    @47
    @10
    disjeq1
    @55
    @13
    @51
    @12
    @8
    @47
    unieq
    eqeq2d
    3anbi123d
    rspcev
    syl13anc
    jca
    ralrimivva
    3jca
    vx
    vy
    vz
    vt
    cS
    cN
    cO
    vs
    rossros.n
    issros
    sylibr
end
