include "cdif.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cmin.mm"
include "cz.mm"
include "elfzelz.mm"
include "3ad2ant2.mm"
include "zred.mm"
include "cc0.mm"
include "wceq.mm"
include "ballotlemiex.mm"
include "simpld.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "1red.mm"
include "readdcld.mm"
include "simp3.mm"
include "zcnd.mm"
include "1cnd.mm"
include "pncand.mm"
include "breqtrrd.mm"
include "ltsub13d.mm"
include "cle.mm"
include "cif.mm"
include "ballotlemsv.mm"
include "3adant3.mm"
include "ltled.mm"
include "iftrued.mm"
include "eqtrd.mm"

theorem ballotlemsgt1
  let vx: setvar x
  let cC: class C
  let cP: class P
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
  assume ballotth.m: |- M e. NN
  assume ballotth.n: |- N e. NN
  assume ballotth.o: |- O = { c e. ~P ( 1 ... ( M + N ) ) | ( # ` c ) = M }
  assume ballotth.p: |- P = ( x e. ~P O |-> ( ( # ` x ) / ( # ` O ) ) )
  assume ballotth.f: |- F = ( c e. O |-> ( i e. ZZ |-> ( ( # ` ( ( 1 ... i ) i^i c ) ) - ( # ` ( ( 1 ... i ) \ c ) ) ) ) )
  assume ballotth.e: |- E = { c e. O | A. i e. ( 1 ... ( M + N ) ) 0 < ( ( F ` c ) ` i ) }
  assume ballotth.mgtn: |- N < M
  assume ballotth.i: |- I = ( c e. ( O \ E ) |-> inf ( { k e. ( 1 ... ( M + N ) ) | ( ( F ` c ) ` k ) = 0 } , RR , < ) )
  assume ballotth.s: |- S = ( c e. ( O \ E ) |-> ( i e. ( 1 ... ( M + N ) ) |-> if ( i <_ ( I ` c ) , ( ( ( I ` c ) + 1 ) - i ) , i ) ) )

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
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint F j
  disjoint c d
  disjoint d k
  assert |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( M + N ) ) /\ J < ( I ` C ) ) -> 1 < ( ( S ` C ) ` J ) )

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
    #
    cfz
    co
    #
    wcel
    #
    cJ
    cC
    cI
    cfv
    #
    clt
    wbr
    #
    w3a
    #
    c1
    @4
    c1
    caddc
    co
    #
    cJ
    cmin
    co
    #
    cJ
    cC
    cS
    cfv
    cfv
    #
    clt
    @6
    cJ
    @7
    c1
    @6
    cJ
    @3
    @0
    cJ
    cz
    wcel
    @5
    cJ
    c1
    @1
    elfzelz
    3ad2ant2
    zred
    #
    @6
    @4
    c1
    @6
    @4
    @0
    @3
    @4
    cz
    wcel
    #
    @5
    @0
    @4
    @2
    wcel
    #
    @11
    @0
    @12
    @4
    cC
    cF
    cfv
    cfv
    cc0
    wceq
    vx
    cC
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
    ballotlemiex
    simpld
    @4
    c1
    @1
    elfzelz
    syl
    3ad2ant1
    #
    zred
    #
    @6
    1red
    #
    readdcld
    @15
    @6
    cJ
    @4
    @7
    c1
    cmin
    co
    clt
    @0
    @3
    @5
    simp3
    #
    @6
    @4
    c1
    @6
    @4
    @13
    zcnd
    @6
    1cnd
    pncand
    breqtrrd
    ltsub13d
    @6
    @9
    cJ
    @4
    cle
    wbr
    #
    @8
    cJ
    cif
    #
    @8
    @0
    @3
    @9
    @18
    wceq
    @5
    vx
    cC
    cP
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
    ballotlemsv
    3adant3
    @6
    @17
    @8
    cJ
    @6
    cJ
    @4
    @10
    @14
    @16
    ltled
    iftrued
    eqtrd
    breqtrrd
end
