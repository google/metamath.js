include "c1.mm"
include "cv.mm"
include "wcel.mm"
include "cdif.mm"
include "crab.mm"
include "wn.mm"
include "cres.mm"
include "wf1o.mm"
include "cen.mm"
include "wbr.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "ballotlem7.mm"
include "cvv.mm"
include "ballotlemoex.mm"
include "difexg.mm"
include "ax-mp.mm"
include "rabex.mm"
include "f1oen.mm"
include "hasheni.mm"
include "mp2b.mm"

theorem ballotlem8
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
  assert |- ( # ` { c e. ( O \ E ) | 1 e. c } ) = ( # ` { c e. ( O \ E ) | -. 1 e. c } )

  proof
    c1
    vc
    cv
    wcel
    #
    vc
    cO
    cE
    cdif
    #
    crab
    #
    @0
    wn
    vc
    @1
    crab
    #
    cR
    @2
    cres
    #
    wf1o
    @2
    @3
    cen
    wbr
    @2
    chash
    cfv
    @3
    chash
    cfv
    wceq
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
    ballotlem7
    @2
    @3
    @4
    @0
    vc
    @1
    cO
    cvv
    wcel
    @1
    cvv
    wcel
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotlemoex
    cO
    cE
    cvv
    difexg
    ax-mp
    rabex
    f1oen
    @2
    @3
    hasheni
    mp2b
end
