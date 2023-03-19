include "cdif.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "wrex.mm"
include "ballotlemro.mm"
include "wceq.mm"
include "ballotlemiex.mm"
include "simpld.mm"
include "cfn.mm"
include "cin.mm"
include "chash.mm"
include "cmin.mm"
include "cmpt2.mm"
include "eqid.mm"
include "ballotlemfrci.mm"
include "0le0.mm"
include "syl6eqbr.mm"
include "fveq2.mm"
include "breq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ballotlemodife.mm"
include "sylanbrc.mm"

theorem ballotlemrc
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
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
  let vu: setvar u
  let vv: setvar v
  let cJ: class J
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
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

  disjoint c k
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
  disjoint w y
  disjoint w z
  disjoint y z
  disjoint c y
  disjoint c z
  disjoint k y
  disjoint k z
  disjoint C y
  disjoint C z
  disjoint F y
  disjoint F z
  disjoint M y
  disjoint M z
  disjoint N y
  disjoint N z
  disjoint k w
  disjoint C w
  disjoint F w
  disjoint M w
  disjoint N w
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
  assert |- ( C e. ( O \ E ) -> ( R ` C ) e. ( O \ E ) )

  proof
    cC
    cO
    cE
    cdif
    #
    wcel
    #
    cC
    cR
    cfv
    #
    cO
    wcel
    vi
    cv
    #
    @2
    cF
    cfv
    #
    cfv
    #
    cc0
    cle
    wbr
    #
    vi
    c1
    cM
    cN
    caddc
    co
    cfz
    co
    #
    wrex
    #
    @2
    @0
    wcel
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
    ballotlemro
    @1
    cC
    cI
    cfv
    #
    @7
    wcel
    #
    @9
    @4
    cfv
    #
    cc0
    cle
    wbr
    #
    @8
    @1
    @10
    @9
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
    @1
    @11
    cc0
    cc0
    cle
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
    vu
    vv
    cfn
    cfn
    vv
    cv
    #
    vu
    cv
    #
    cin
    chash
    cfv
    @13
    @14
    cdif
    chash
    cfv
    cmin
    co
    cmpt2
    #
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
    @15
    eqid
    ballotlemfrci
    0le0
    syl6eqbr
    @6
    @12
    vi
    @9
    @7
    @3
    @9
    wceq
    @5
    @11
    cc0
    cle
    @3
    @9
    @4
    fveq2
    breq1d
    rspcev
    syl2anc
    vx
    @2
    cP
    vi
    cE
    cF
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
    ballotlemodife
    sylanbrc
end
