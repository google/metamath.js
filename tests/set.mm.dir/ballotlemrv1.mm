include "cdif.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cmin.mm"
include "cif.mm"
include "wb.mm"
include "ballotlemrv.mm"
include "3adant3.mm"
include "iftrue.mm"
include "eleq1d.mm"
include "3ad2ant3.mm"
include "bitrd.mm"

theorem ballotlemrv1
  let vx: setvar x
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let vi: setvar i
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cI: class I
  let cJ: class J
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
  let vj: setvar j
  let vd: setvar d
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
  disjoint C i
  disjoint i k
  disjoint E i
  disjoint E k
  disjoint C k
  disjoint I k
  disjoint c k
  disjoint E c
  disjoint I i
  disjoint I c
  disjoint J k
  disjoint S k
  disjoint S i
  disjoint S c
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint F j
  disjoint c d
  disjoint d k
  disjoint i j
  disjoint I j
  disjoint C j
  disjoint E j
  disjoint J j
  disjoint j k
  disjoint S j
  disjoint D i
  disjoint D k
  assert |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( M + N ) ) /\ J <_ ( I ` C ) ) -> ( J e. ( R ` C ) <-> ( ( ( I ` C ) + 1 ) - J ) e. C ) )

  proof
    cC
    cO
    cE
    cdif
    wcel
    #
    cJ
    c1
    cM
    cN
    caddc
    co
    cfz
    co
    wcel
    #
    cJ
    cC
    cI
    cfv
    #
    cle
    wbr
    #
    w3a
    cJ
    cC
    cR
    cfv
    wcel
    #
    @3
    @2
    c1
    caddc
    co
    cJ
    cmin
    co
    #
    cJ
    cif
    #
    cC
    wcel
    #
    @5
    cC
    wcel
    #
    @0
    @1
    @4
    @7
    wb
    @3
    vx
    cC
    cP
    cR
    cS
    vi
    vk
    cE
    cF
    cI
    cJ
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
    ballotlemrv
    3adant3
    @3
    @0
    @7
    @8
    wb
    @1
    @3
    @6
    @5
    cC
    @3
    @5
    cJ
    iftrue
    eleq1d
    3ad2ant3
    bitrd
end
