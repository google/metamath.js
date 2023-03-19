include "cdif.mm"
include "wcel.mm"
include "cc0.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "wa.mm"
include "cfv.mm"
include "c1.mm"
include "cin.mm"
include "chash.mm"
include "cmin.mm"
include "eldifi.mm"
include "adantr.mm"
include "cz.mm"
include "elfzelz.mm"
include "adantl.mm"
include "ballotlemfval.mm"
include "cfn.mm"
include "wceq.mm"
include "wss.mm"
include "fzfi.mm"
include "ballotlemelo.mm"
include "simplbi.mm"
include "ssfi.mm"
include "sylancr.mm"
include "syl.mm"
include "fzfid.mm"
include "ballotlemgval.mm"
include "syl2anc.mm"
include "eqtr4d.mm"

theorem ballotlemfg
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
  let cJ: class J
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
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
  disjoint J u
  disjoint J v
  disjoint R u
  disjoint R v
  disjoint S u
  disjoint S v
  disjoint J i
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
  disjoint R i
  disjoint U u
  disjoint U v
  disjoint V u
  disjoint V v
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
  assert |- ( ( C e. ( O \ E ) /\ J e. ( 0 ... ( M + N ) ) ) -> ( ( F ` C ) ` J ) = ( C .^ ( 1 ... J ) ) )

  proof
    cC
    cO
    cE
    cdif
    wcel
    #
    cJ
    cc0
    cM
    cN
    caddc
    co
    #
    cfz
    co
    wcel
    #
    wa
    #
    cJ
    cC
    cF
    cfv
    cfv
    c1
    cJ
    cfz
    co
    #
    cC
    cin
    chash
    cfv
    @4
    cC
    cdif
    chash
    cfv
    cmin
    co
    #
    cC
    @4
    c.ex
    co
    #
    @3
    vx
    cC
    cP
    vi
    cF
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
    @0
    cC
    cO
    wcel
    #
    @2
    cC
    cO
    cE
    eldifi
    adantr
    #
    @2
    cJ
    cz
    wcel
    @0
    cJ
    cc0
    @1
    elfzelz
    adantl
    ballotlemfval
    @3
    cC
    cfn
    wcel
    #
    @4
    cfn
    wcel
    @6
    @5
    wceq
    @3
    @7
    @9
    @8
    @7
    c1
    @1
    cfz
    co
    #
    cfn
    wcel
    cC
    @10
    wss
    #
    @9
    c1
    @1
    fzfi
    @7
    @11
    cC
    chash
    cfv
    cM
    wceq
    cC
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotlemelo
    simplbi
    @10
    cC
    ssfi
    sylancr
    syl
    @3
    c1
    cJ
    fzfid
    vx
    vv
    vu
    cP
    cR
    cS
    cC
    vi
    vk
    cE
    c.ex
    cF
    cI
    cM
    cN
    cO
    @4
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
    ballotlemgval
    syl2anc
    eqtr4d
end
