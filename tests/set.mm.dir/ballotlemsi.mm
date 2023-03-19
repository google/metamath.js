include "cdif.mm"
include "wcel.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cif.mm"
include "cfz.mm"
include "wceq.mm"
include "cc0.mm"
include "ballotlemiex.mm"
include "simpld.mm"
include "ballotlemsv.mm"
include "mpdan.mm"
include "cr.mm"
include "elfzelz.mm"
include "zred.mm"
include "syl.mm"
include "leidd.mm"
include "iftrued.mm"
include "recnd.mm"
include "1cnd.mm"
include "pncan2d.mm"
include "3eqtrd.mm"

theorem ballotlemsi
  let vx: setvar x
  let cC: class C
  let cP: class P
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
  let vd: setvar d
  let cJ: class J
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
  disjoint i j
  disjoint I j
  disjoint C j
  disjoint E j
  disjoint J j
  assert |- ( C e. ( O \ E ) -> ( ( S ` C ) ` ( I ` C ) ) = 1 )

  proof
    cC
    cO
    cE
    cdif
    wcel
    #
    cC
    cI
    cfv
    #
    cC
    cS
    cfv
    cfv
    #
    @1
    @1
    cle
    wbr
    #
    @1
    c1
    caddc
    co
    @1
    cmin
    co
    #
    @1
    cif
    #
    @4
    c1
    @0
    @1
    c1
    cM
    cN
    caddc
    co
    #
    cfz
    co
    wcel
    #
    @2
    @5
    wceq
    @0
    @7
    @1
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
    #
    vx
    cC
    cP
    cS
    vi
    vk
    cE
    cF
    cI
    @1
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
    mpdan
    @0
    @3
    @4
    @1
    @0
    @1
    @0
    @7
    @1
    cr
    wcel
    @8
    @7
    @1
    @1
    c1
    @6
    elfzelz
    zred
    syl
    #
    leidd
    iftrued
    @0
    @1
    c1
    @0
    @1
    @9
    recnd
    @0
    1cnd
    pncan2d
    3eqtrd
end
