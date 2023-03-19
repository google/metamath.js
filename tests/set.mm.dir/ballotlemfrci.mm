include "cdif.mm"
include "wcel.mm"
include "cfv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "caddc.mm"
include "cuz.mm"
include "ballotlemiex.mm"
include "simpld.mm"
include "elfzuz.mm"
include "eluzfz2.mm"
include "3syl.mm"
include "ballotlemfrc.mm"
include "mpdan.mm"
include "ballotlemsi.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "wss.mm"
include "1eluzge0.mm"
include "fzss1.mm"
include "ax-mp.mm"
include "sseldi.mm"
include "ballotlemfg.mm"
include "simprd.mm"
include "3eqtr2d.mm"

theorem ballotlemfrci
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let vi: setvar i
  let vk: setvar k
  let cE: class E
  let c.ex: class .^
  let cF: class F
  let cI: class I
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
  let cJ: class J
  let cU: class U
  let cV: class V
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
  assume ballotlemg: |- .^ = ( u e. Fin , v e. Fin |-> ( ( # ` ( v i^i u ) ) - ( # ` ( v \ u ) ) ) )

  disjoint u v
  disjoint C u
  disjoint C v
  disjoint I u
  disjoint I v
  disjoint R u
  disjoint R v
  disjoint S u
  disjoint S v
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
  disjoint S k
  disjoint S i
  disjoint S c
  disjoint R i
  disjoint J u
  disjoint J v
  disjoint U u
  disjoint U v
  disjoint V u
  disjoint V v
  disjoint J i
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
  disjoint J k
  disjoint D i
  disjoint D k
  assert |- ( C e. ( O \ E ) -> ( ( F ` ( R ` C ) ) ` ( I ` C ) ) = 0 )

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
    cR
    cfv
    cF
    cfv
    cfv
    #
    cC
    c1
    @1
    cfz
    co
    #
    c.ex
    co
    #
    @1
    cC
    cF
    cfv
    cfv
    #
    cc0
    @0
    @2
    cC
    @1
    cC
    cS
    cfv
    cfv
    #
    @1
    cfz
    co
    #
    c.ex
    co
    #
    @4
    @0
    @1
    @3
    wcel
    #
    @2
    @8
    wceq
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
    #
    wcel
    #
    @1
    c1
    cuz
    cfv
    wcel
    @9
    @0
    @12
    @5
    cc0
    wceq
    #
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
    #
    simpld
    #
    @1
    c1
    @10
    elfzuz
    c1
    @1
    eluzfz2
    3syl
    vx
    vv
    vu
    cC
    cP
    cR
    cS
    vi
    vk
    cE
    c.ex
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
    ballotth.r
    ballotlemg
    ballotlemfrc
    mpdan
    @0
    @7
    @3
    cC
    c.ex
    @0
    @6
    c1
    @1
    cfz
    vx
    cC
    cP
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
    ballotlemsi
    oveq1d
    oveq2d
    eqtrd
    @0
    @1
    cc0
    @10
    cfz
    co
    #
    wcel
    @5
    @4
    wceq
    @0
    @11
    @16
    @1
    c1
    cc0
    cuz
    cfv
    wcel
    @11
    @16
    wss
    1eluzge0
    c1
    cc0
    @10
    fzss1
    ax-mp
    @15
    sseldi
    vx
    vv
    vu
    cC
    cP
    cR
    cS
    vi
    vk
    cE
    c.ex
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
    ballotth.r
    ballotlemg
    ballotlemfg
    mpdan
    @0
    @12
    @13
    @14
    simprd
    3eqtr2d
end
