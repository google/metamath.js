include "cdif.mm"
include "cv.mm"
include "cfv.mm"
include "cima.mm"
include "cmpt.mm"
include "ccnv.mm"
include "wceq.mm"
include "wtru.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "ballotlemrinv0.mm"
include "impbii.mm"
include "a1i.mm"
include "mptcnv.mm"
include "trud.mm"
include "fveq2.mm"
include "id.mm"
include "imaeq12d.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "cnveqi.mm"
include "3eqtr4i.mm"

theorem ballotlemrinv
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
  let vd: setvar d
  let vj: setvar j
  let cC: class C
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

  disjoint i x
  disjoint i k
  disjoint k x
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
  disjoint d i
  disjoint d x
  disjoint d k
  disjoint E d
  disjoint I d
  disjoint O d
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
  assert |- `' R = R

  proof
    vc
    cO
    cE
    cdif
    #
    vc
    cv
    #
    cS
    cfv
    #
    @1
    cima
    #
    cmpt
    #
    ccnv
    #
    @4
    cR
    ccnv
    cR
    @5
    vd
    @0
    vd
    cv
    #
    cS
    cfv
    #
    @6
    cima
    #
    cmpt
    #
    @4
    @5
    @9
    wceq
    wtru
    vc
    vd
    @0
    @3
    @0
    @8
    @1
    @0
    wcel
    @6
    @3
    wceq
    wa
    #
    @6
    @0
    wcel
    @1
    @8
    wceq
    wa
    #
    wb
    wtru
    @10
    @11
    vx
    @1
    @6
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
    ballotlemrinv0
    vx
    @6
    @1
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
    ballotlemrinv0
    impbii
    a1i
    mptcnv
    trud
    vd
    vc
    @0
    @8
    @3
    @6
    @1
    wceq
    #
    @7
    @2
    @6
    @1
    @6
    @1
    cS
    fveq2
    @12
    id
    imaeq12d
    cbvmptv
    eqtri
    cR
    @4
    ballotth.r
    cnveqi
    ballotth.r
    3eqtr4i
end
