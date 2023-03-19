include "ccvm.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "w3a.mm"
include "ccnv.mm"
include "cima.mm"
include "crest.mm"
include "cuni.mm"
include "csn.mm"
include "cdif.mm"
include "ccld.mm"
include "ctop.mm"
include "wss.mm"
include "wceq.mm"
include "cvmtop1.mm"
include "3ad2ant1.mm"
include "cvmsuni.mm"
include "3ad2ant2.mm"
include "cvmsss.mm"
include "unissd.mm"
include "eqsstr3d.mm"
include "eqid.mm"
include "restuni.mm"
include "syl2anc.mm"
include "difeq1d.mm"
include "cun.mm"
include "unisng.mm"
include "3ad2ant3.mm"
include "uneq2d.mm"
include "uniun.mm"
include "undif1.mm"
include "simp3.mm"
include "snssd.mm"
include "ssequn2.mm"
include "sylib.mm"
include "syl5eq.mm"
include "unieqd.mm"
include "eqtrd.mm"
include "syl5eqr.mm"
include "eqtr3d.mm"
include "cin.mm"
include "c0.mm"
include "wb.mm"
include "difss.mm"
include "unissi.mm"
include "syl5sseq.mm"
include "cv.mm"
include "ciun.mm"
include "uniiun.mm"
include "ineq2i.mm"
include "incom.mm"
include "iunin2.mm"
include "3eqtr4i.mm"
include "wa.mm"
include "wne.mm"
include "eldifsn.mm"
include "wn.mm"
include "nesym.mm"
include "wo.mm"
include "cvmsdisj.mm"
include "3expa.mm"
include "ord.mm"
include "syl5bi.mm"
include "impr.mm"
include "sylan2b.mm"
include "iuneq2dv.mm"
include "3adant1.mm"
include "iun0.mm"
include "syl6eq.mm"
include "uneqdifeq.mm"
include "mpbid.mm"
include "cvv.mm"
include "uniexg.mm"
include "eqeltrrd.mm"
include "resttop.mm"
include "elssuni.mm"
include "adantl.mm"
include "adantr.mm"
include "sseqtrd.mm"
include "df-ss.mm"
include "sselda.mm"
include "elrestr.mm"
include "syl3anc.mm"
include "ex.mm"
include "ssrdv.mm"
include "ssdifssd.mm"
include "uniopn.mm"
include "opncld.mm"

theorem cvmscld
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cC: class C
  let cS: class S
  let cT: class T
  let cU: class U
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vt: setvar t
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cV: class V
  let cW: class W
  let cX: class X
  let cB: class B
  assume cvmcov.1: |- S = ( k e. J |-> { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\ A. u e. s ( A. v e. ( s \ { u } ) ( u i^i v ) = (/) /\ ( F |` u ) e. ( ( C |`t u ) Homeo ( J |`t k ) ) ) ) } )

  disjoint k s
  disjoint k u
  disjoint k v
  disjoint C k
  disjoint s u
  disjoint s v
  disjoint C s
  disjoint u v
  disjoint C u
  disjoint C v
  disjoint F k
  disjoint F s
  disjoint F u
  disjoint F v
  disjoint J k
  disjoint J s
  disjoint J u
  disjoint J v
  disjoint U k
  disjoint U s
  disjoint U u
  disjoint U v
  disjoint T s
  disjoint T u
  disjoint T v
  disjoint A u
  disjoint A v
  disjoint a b
  disjoint a k
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint C a
  disjoint b k
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint C b
  disjoint k t
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint C t
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint C w
  disjoint x y
  disjoint x z
  disjoint C x
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint F a
  disjoint F b
  disjoint F t
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint P k
  disjoint P x
  disjoint P y
  disjoint J a
  disjoint J b
  disjoint J t
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint S t
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint U t
  disjoint U w
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint T x
  disjoint T z
  disjoint V a
  disjoint V b
  disjoint V k
  disjoint V s
  disjoint V t
  disjoint V u
  disjoint V v
  disjoint V w
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint W v
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint A t
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B t
  disjoint B v
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  assert |- ( ( F e. ( C CovMap J ) /\ T e. ( S ` U ) /\ A e. T ) -> A e. ( Clsd ` ( C |`t ( `' F " U ) ) ) )

  proof
    cF
    cC
    cJ
    ccvm
    co
    wcel
    #
    cT
    cU
    cS
    cfv
    #
    wcel
    #
    cA
    cT
    wcel
    #
    w3a
    #
    cC
    cF
    ccnv
    cU
    cima
    #
    crest
    co
    #
    cuni
    #
    cT
    cA
    csn
    #
    cdif
    #
    cuni
    #
    cdif
    #
    cA
    @6
    ccld
    cfv
    #
    @4
    @5
    @10
    cdif
    #
    @11
    cA
    @4
    @5
    @7
    @10
    @4
    cC
    ctop
    wcel
    #
    @5
    cC
    cuni
    #
    wss
    @5
    @7
    wceq
    @0
    @2
    @14
    @3
    cC
    cF
    cJ
    cvmtop1
    3ad2ant1
    #
    @4
    @5
    cT
    cuni
    #
    @15
    @2
    @0
    @17
    @5
    wceq
    #
    @3
    vv
    vu
    cC
    cS
    cT
    cU
    vk
    cF
    cJ
    vs
    cvmcov.1
    cvmsuni
    3ad2ant2
    #
    @4
    cT
    cC
    @2
    @0
    cT
    cC
    wss
    @3
    vv
    vu
    cC
    cS
    cT
    cU
    vk
    cF
    cJ
    vs
    cvmcov.1
    cvmsss
    3ad2ant2
    #
    unissd
    eqsstr3d
    @5
    cC
    @15
    @15
    eqid
    restuni
    syl2anc
    difeq1d
    @4
    @10
    cA
    cun
    #
    @5
    wceq
    #
    @13
    cA
    wceq
    #
    @4
    @10
    @8
    cuni
    #
    cun
    #
    @21
    @5
    @4
    @24
    cA
    @10
    @3
    @0
    @24
    cA
    wceq
    @2
    cA
    cT
    unisng
    3ad2ant3
    uneq2d
    @4
    @25
    @9
    @8
    cun
    #
    cuni
    #
    @5
    @9
    @8
    uniun
    @4
    @27
    @17
    @5
    @4
    @26
    cT
    @4
    @26
    cT
    @8
    cun
    #
    cT
    cT
    @8
    undif1
    @4
    @8
    cT
    wss
    @28
    cT
    wceq
    @4
    cA
    cT
    @0
    @2
    @3
    simp3
    snssd
    @8
    cT
    ssequn2
    sylib
    syl5eq
    unieqd
    @19
    eqtrd
    syl5eqr
    eqtr3d
    @4
    @10
    @5
    wss
    @10
    cA
    cin
    #
    c0
    wceq
    @22
    @23
    wb
    @4
    @17
    @10
    @5
    @9
    cT
    cT
    @8
    difss
    unissi
    @19
    syl5sseq
    @4
    @29
    vx
    @9
    cA
    vx
    cv
    #
    cin
    #
    ciun
    #
    c0
    cA
    @10
    cin
    cA
    vx
    @9
    @30
    ciun
    #
    cin
    @29
    @32
    @10
    @33
    cA
    vx
    @9
    uniiun
    ineq2i
    @10
    cA
    incom
    vx
    @9
    cA
    @30
    iunin2
    3eqtr4i
    @4
    @32
    vx
    @9
    c0
    ciun
    #
    c0
    @2
    @3
    @32
    @34
    wceq
    @0
    @2
    @3
    wa
    #
    vx
    @9
    @31
    c0
    @30
    @9
    wcel
    @35
    @30
    cT
    wcel
    #
    @30
    cA
    wne
    #
    wa
    @31
    c0
    wceq
    #
    @30
    cT
    cA
    eldifsn
    @35
    @36
    @37
    @38
    @37
    cA
    @30
    wceq
    #
    wn
    @35
    @36
    wa
    #
    @38
    @30
    cA
    nesym
    @40
    @39
    @38
    @2
    @3
    @36
    @39
    @38
    wo
    vv
    vu
    cA
    @30
    cC
    cS
    cT
    cU
    vk
    cF
    cJ
    vs
    cvmcov.1
    cvmsdisj
    3expa
    ord
    syl5bi
    impr
    sylan2b
    iuneq2dv
    3adant1
    vx
    @9
    iun0
    syl6eq
    syl5eq
    @10
    cA
    @5
    uneqdifeq
    syl2anc
    mpbid
    eqtr3d
    @4
    @6
    ctop
    wcel
    #
    @10
    @6
    wcel
    #
    @11
    @12
    wcel
    @4
    @14
    @5
    cvv
    wcel
    #
    @41
    @16
    @4
    @17
    @5
    cvv
    @19
    @2
    @0
    @17
    cvv
    wcel
    @3
    cT
    @1
    uniexg
    3ad2ant2
    eqeltrrd
    #
    @5
    cC
    cvv
    resttop
    syl2anc
    #
    @4
    @41
    @9
    @6
    wss
    @42
    @45
    @4
    cT
    @6
    @8
    @4
    vx
    cT
    @6
    @4
    @36
    @30
    @6
    wcel
    @4
    @36
    wa
    #
    @30
    @5
    cin
    #
    @30
    @6
    @46
    @30
    @5
    wss
    @47
    @30
    wceq
    @46
    @30
    @17
    @5
    @36
    @30
    @17
    wss
    @4
    @30
    cT
    elssuni
    adantl
    @4
    @18
    @36
    @19
    adantr
    sseqtrd
    @30
    @5
    df-ss
    sylib
    @46
    @14
    @43
    @30
    cC
    wcel
    @47
    @6
    wcel
    @4
    @14
    @36
    @16
    adantr
    @4
    @43
    @36
    @44
    adantr
    @4
    cT
    cC
    @30
    @20
    sselda
    @30
    @5
    cC
    ctop
    cvv
    elrestr
    syl3anc
    eqeltrrd
    ex
    ssrdv
    ssdifssd
    @9
    @6
    uniopn
    syl2anc
    @10
    @6
    @7
    @7
    eqid
    opncld
    syl2anc
    eqeltrrd
end
