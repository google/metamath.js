include "c1.mm"
include "cv.mm"
include "wcel.mm"
include "cdif.mm"
include "crab.mm"
include "wn.mm"
include "cfv.mm"
include "cima.mm"
include "funmpt2.mm"
include "ballotlemrinv.mm"
include "wss.mm"
include "wral.mm"
include "wa.mm"
include "rabid.mm"
include "ballotlemrc.mm"
include "adantr.mm"
include "ballotlem1c.mm"
include "ex.mm"
include "ballotlem1ri.mm"
include "notbid.mm"
include "sylibrd.mm"
include "imp.mm"
include "jca.mm"
include "sylbi.mm"
include "rgen.mm"
include "wceq.mm"
include "eleq2.mm"
include "elrab.mm"
include "cbvrabv.mm"
include "eleq2i.mm"
include "bitr3i.mm"
include "ralbii.mm"
include "mpbi.mm"
include "wfun.mm"
include "cdm.mm"
include "wb.mm"
include "ssrab2.mm"
include "cvv.mm"
include "fvex.mm"
include "imaexg.mm"
include "ax-mp.mm"
include "dmmpti.mm"
include "sseqtr4i.mm"
include "nfrab1.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "funimass4f.mm"
include "mp2an.mm"
include "mpbir.mm"
include "ballotlemic.mm"
include "rinvf1o.mm"

theorem ballotlem7
  let vx: setvar x
  let cP: class P
  let cR: class R
  let cS: class S
  let vi: setvar i
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cI: class I
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
  let vb: setvar b
  let vj: setvar j
  let cC: class C
  let vd: setvar d
  let cJ: class J
  let cD: class D
  assume ballotth.m: |- M e. NN
  assume ballotth.n: |- N e. NN
  assume ballotth.o: |- O = { c e. ~P ( 1 ... ( M + N ) ) | ( # ` c ) = M }
  assume ballotth.p: |- P = ( x e. ~P O |-> ( ( # ` x ) / ( # ` O ) ) )
  assume ballotth.f: |- F = ( c e. O |-> ( i e. ZZ |-> ( ( # ` ( ( 1 ... i ) i^i c ) ) - ( # ` ( ( 1 ... i ) \ c ) ) ) ) )
  assume ballotth.e: |- E = { c e. O | A. i e. ( 1 ... ( M + N ) ) 0 < ( ( F ` c ) ` i ) }
  assume ballotth.mgtn: |- N < M
  assume ballotth.i: |- I = ( c e. ( O \ E ) |-> inf ( { k e. ( 1 ... ( M + N ) ) | ( ( F ` c ) ` k ) = 0 } , RR , < ) )
  assume ballotth.s: |- S = ( c e. ( O \ E ) |-> ( i e. ( 1 ... ( M + N ) ) |-> if ( i <_ ( I ` c ) , ( ( ( I ` c ) + 1 ) - i ) , i ) ) )
  assume ballotth.r: |- R = ( c e. ( O \ E ) |-> ( ( S ` c ) " c ) )

  disjoint O c
  disjoint M c
  disjoint N c
  disjoint O c
  disjoint M i
  disjoint N i
  disjoint O i
  disjoint M k
  disjoint N k
  disjoint O k
  disjoint c i
  disjoint F c
  disjoint F i
  disjoint F k
  disjoint i k
  disjoint E i
  disjoint E k
  disjoint I k
  disjoint c k
  disjoint E c
  disjoint I i
  disjoint I c
  disjoint S k
  disjoint S i
  disjoint S c
  disjoint R i
  disjoint R k
  disjoint c x
  disjoint F x
  disjoint M x
  disjoint N x
  disjoint k x
  disjoint i x
  disjoint E b
  disjoint b c
  disjoint O b
  disjoint R b
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint F j
  disjoint C i
  disjoint C k
  disjoint c d
  disjoint d k
  disjoint i j
  disjoint I j
  disjoint C j
  disjoint E j
  disjoint J j
  disjoint j k
  disjoint S j
  disjoint J k
  disjoint D i
  disjoint D k
  disjoint C x
  disjoint S d
  assert |- ( R |` { c e. ( O \ E ) | 1 e. c } ) : { c e. ( O \ E ) | 1 e. c } -1-1-onto-> { c e. ( O \ E ) | -. 1 e. c }

  proof
    c1
    vc
    cv
    #
    wcel
    #
    vc
    cO
    cE
    cdif
    #
    crab
    #
    @1
    wn
    #
    vc
    @2
    crab
    #
    cR
    vc
    @2
    @0
    cS
    cfv
    #
    @0
    cima
    #
    cR
    ballotth.r
    funmpt2
    #
    vx
    cP
    cR
    cS
    vi
    vk
    cE
    cF
    cI
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    ballotth.e
    ballotth.mgtn
    ballotth.i
    ballotth.s
    ballotth.r
    ballotlemrinv
    cR
    @3
    cima
    @5
    wss
    #
    @0
    cR
    cfv
    #
    @5
    wcel
    #
    vc
    @3
    wral
    #
    @10
    @2
    wcel
    #
    c1
    @10
    wcel
    #
    wn
    #
    wa
    #
    vc
    @3
    wral
    @12
    @16
    vc
    @3
    @0
    @3
    wcel
    @0
    @2
    wcel
    #
    @1
    wa
    #
    @16
    @1
    vc
    @2
    rabid
    @18
    @13
    @15
    @17
    @13
    @1
    vx
    @0
    cP
    cR
    cS
    vi
    vk
    cE
    cF
    cI
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    ballotth.e
    ballotth.mgtn
    ballotth.i
    ballotth.s
    ballotth.r
    ballotlemrc
    #
    adantr
    @17
    @1
    @15
    @17
    @1
    @0
    cI
    cfv
    @0
    wcel
    #
    wn
    #
    @15
    @17
    @1
    @21
    vx
    @0
    cP
    vi
    vk
    cE
    cF
    cI
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    ballotth.e
    ballotth.mgtn
    ballotth.i
    ballotlem1c
    ex
    @17
    @14
    @20
    vx
    @0
    cP
    cR
    cS
    vi
    vk
    cE
    cF
    cI
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    ballotth.e
    ballotth.mgtn
    ballotth.i
    ballotth.s
    ballotth.r
    ballotlem1ri
    #
    notbid
    sylibrd
    imp
    jca
    sylbi
    rgen
    @16
    @11
    vc
    @3
    @16
    @10
    c1
    vb
    cv
    #
    wcel
    #
    wn
    #
    vb
    @2
    crab
    #
    wcel
    @11
    @25
    @15
    vb
    @10
    @2
    @23
    @10
    wceq
    @24
    @14
    @23
    @10
    c1
    eleq2
    #
    notbid
    elrab
    @26
    @5
    @10
    @25
    @4
    vb
    vc
    @2
    @23
    @0
    wceq
    @24
    @1
    @23
    @0
    c1
    eleq2
    #
    notbid
    cbvrabv
    eleq2i
    bitr3i
    ralbii
    mpbi
    cR
    wfun
    #
    @3
    cR
    cdm
    #
    wss
    @9
    @12
    wb
    @8
    @3
    @2
    @30
    @1
    vc
    @2
    ssrab2
    vc
    @2
    @7
    cR
    @6
    cvv
    wcel
    @7
    cvv
    wcel
    @0
    cS
    fvex
    @6
    @0
    cvv
    imaexg
    ax-mp
    ballotth.r
    dmmpti
    #
    sseqtr4i
    #
    vc
    @3
    @5
    cR
    @1
    vc
    @2
    nfrab1
    #
    @4
    vc
    @2
    nfrab1
    #
    vc
    cR
    vc
    @2
    @7
    cmpt
    ballotth.r
    vc
    @2
    @7
    nfmpt1
    nfcxfr
    #
    funimass4f
    mp2an
    mpbir
    cR
    @5
    cima
    @3
    wss
    #
    @10
    @3
    wcel
    #
    vc
    @5
    wral
    #
    @13
    @14
    wa
    #
    vc
    @5
    wral
    @38
    @39
    vc
    @5
    @0
    @5
    wcel
    @17
    @4
    wa
    #
    @39
    @4
    vc
    @2
    rabid
    @40
    @13
    @14
    @17
    @13
    @4
    @19
    adantr
    @17
    @4
    @14
    @17
    @4
    @20
    @14
    @17
    @4
    @20
    vx
    @0
    cP
    vi
    vk
    cE
    cF
    cI
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    ballotth.e
    ballotth.mgtn
    ballotth.i
    ballotlemic
    ex
    @22
    sylibrd
    imp
    jca
    sylbi
    rgen
    @39
    @37
    vc
    @5
    @39
    @10
    @24
    vb
    @2
    crab
    #
    wcel
    @37
    @24
    @14
    vb
    @10
    @2
    @27
    elrab
    @41
    @3
    @10
    @24
    @1
    vb
    vc
    @2
    @28
    cbvrabv
    eleq2i
    bitr3i
    ralbii
    mpbi
    @29
    @5
    @30
    wss
    @36
    @38
    wb
    @8
    @5
    @2
    @30
    @4
    vc
    @2
    ssrab2
    @31
    sseqtr4i
    #
    vc
    @5
    @3
    cR
    @34
    @33
    @35
    funimass4f
    mp2an
    mpbir
    @32
    @42
    rinvf1o
end
